theory HOL4Base = HOL4Compat + HOL4Syntax:

;setup_theory bool

constdefs
  ARB :: "'a" 
  "ARB == SOME x. True"

lemma ARB_DEF: "ARB = (SOME x. True)"
  by (import bool ARB_DEF)

constdefs
  IN :: "'a => ('a => bool) => bool" 
  "IN == %x f. f x"

lemma IN_DEF: "IN = (%x f. f x)"
  by (import bool IN_DEF)

constdefs
  RES_FORALL :: "('a => bool) => ('a => bool) => bool" 
  "RES_FORALL == %p m. ALL x. IN x p --> m x"

lemma RES_FORALL_DEF: "RES_FORALL = (%p m. ALL x. IN x p --> m x)"
  by (import bool RES_FORALL_DEF)

constdefs
  RES_EXISTS :: "('a => bool) => ('a => bool) => bool" 
  "RES_EXISTS == %p m. EX x. IN x p & m x"

lemma RES_EXISTS_DEF: "RES_EXISTS = (%p m. EX x. IN x p & m x)"
  by (import bool RES_EXISTS_DEF)

constdefs
  RES_EXISTS_UNIQUE :: "('a => bool) => ('a => bool) => bool" 
  "RES_EXISTS_UNIQUE ==
%p m. RES_EXISTS p m &
      RES_FORALL p (%x. RES_FORALL p (%y. m x & m y --> x = y))"

lemma RES_EXISTS_UNIQUE_DEF: "RES_EXISTS_UNIQUE =
(%p m. RES_EXISTS p m &
       RES_FORALL p (%x. RES_FORALL p (%y. m x & m y --> x = y)))"
  by (import bool RES_EXISTS_UNIQUE_DEF)

constdefs
  RES_SELECT :: "('a => bool) => ('a => bool) => 'a" 
  "RES_SELECT == %p m. SOME x. IN x p & m x"

lemma RES_SELECT_DEF: "RES_SELECT = (%p m. SOME x. IN x p & m x)"
  by (import bool RES_SELECT_DEF)

lemma EXCLUDED_MIDDLE: "ALL t. t | ~ t"
  by (import bool EXCLUDED_MIDDLE)

lemma FORALL_THM: "All f = All f"
  by (import bool FORALL_THM)

lemma EXISTS_THM: "Ex f = Ex f"
  by (import bool EXISTS_THM)

lemma F_IMP: "ALL t. ~ t --> t --> False"
  by (import bool F_IMP)

lemma NOT_AND: "~ (t & ~ t)"
  by (import bool NOT_AND)

lemma AND_CLAUSES: "ALL t.
   (True & t) = t &
   (t & True) = t & (False & t) = False & (t & False) = False & (t & t) = t"
  by (import bool AND_CLAUSES)

lemma OR_CLAUSES: "ALL t.
   (True | t) = True &
   (t | True) = True & (False | t) = t & (t | False) = t & (t | t) = t"
  by (import bool OR_CLAUSES)

lemma IMP_CLAUSES: "ALL t.
   (True --> t) = t &
   (t --> True) = True &
   (False --> t) = True & (t --> t) = True & (t --> False) = (~ t)"
  by (import bool IMP_CLAUSES)

lemma NOT_CLAUSES: "(ALL t. (~ ~ t) = t) & (~ True) = False & (~ False) = True"
  by (import bool NOT_CLAUSES)

lemma BOOL_EQ_DISTINCT: "True ~= False & False ~= True"
  by (import bool BOOL_EQ_DISTINCT)

lemma EQ_CLAUSES: "ALL t.
   (True = t) = t &
   (t = True) = t & (False = t) = (~ t) & (t = False) = (~ t)"
  by (import bool EQ_CLAUSES)

lemma COND_CLAUSES: "ALL t1 t2. (if True then t1 else t2) = t1 & (if False then t1 else t2) = t2"
  by (import bool COND_CLAUSES)

lemma SELECT_UNIQUE: "ALL P x. (ALL y. P y = (y = x)) --> Eps P = x"
  by (import bool SELECT_UNIQUE)

lemma BOTH_EXISTS_AND_THM: "ALL (P::bool) Q::bool. (EX x::'a. P & Q) = ((EX x::'a. P) & (EX x::'a. Q))"
  by (import bool BOTH_EXISTS_AND_THM)

lemma BOTH_FORALL_OR_THM: "ALL (P::bool) Q::bool.
   (ALL x::'a. P | Q) = ((ALL x::'a. P) | (ALL x::'a. Q))"
  by (import bool BOTH_FORALL_OR_THM)

lemma BOTH_FORALL_IMP_THM: "ALL (P::bool) Q::bool.
   (ALL x::'a. P --> Q) = ((EX x::'a. P) --> (ALL x::'a. Q))"
  by (import bool BOTH_FORALL_IMP_THM)

lemma BOTH_EXISTS_IMP_THM: "ALL (P::bool) Q::bool.
   (EX x::'a. P --> Q) = ((ALL x::'a. P) --> (EX x::'a. Q))"
  by (import bool BOTH_EXISTS_IMP_THM)

lemma OR_IMP_THM: "ALL A B. (A = (B | A)) = (B --> A)"
  by (import bool OR_IMP_THM)

lemma DE_MORGAN_THM: "ALL A B. (~ (A & B)) = (~ A | ~ B) & (~ (A | B)) = (~ A & ~ B)"
  by (import bool DE_MORGAN_THM)

lemma IMP_F_EQ_F: "ALL t. (t --> False) = (t = False)"
  by (import bool IMP_F_EQ_F)

lemma EQ_EXPAND: "ALL t1 t2. (t1 = t2) = (t1 & t2 | ~ t1 & ~ t2)"
  by (import bool EQ_EXPAND)

lemma COND_RATOR: "ALL b f g x. (if b then f else g) x = (if b then f x else g x)"
  by (import bool COND_RATOR)

lemma COND_ABS: "ALL b f g. (%x. if b then f x else g x) = (if b then f else g)"
  by (import bool COND_ABS)

lemma COND_EXPAND: "ALL b t1 t2. (if b then t1 else t2) = ((~ b | t1) & (b | t2))"
  by (import bool COND_EXPAND)

lemma ONE_ONE_THM: "ALL f. inj f = (ALL x1 x2. f x1 = f x2 --> x1 = x2)"
  by (import bool ONE_ONE_THM)

lemma ABS_REP_THM: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (op -->::bool => bool => bool)
      ((Ex::(('b => 'a) => bool) => bool)
        ((TYPE_DEFINITION::('a => bool) => ('b => 'a) => bool) P))
      ((Ex::(('b => 'a) => bool) => bool)
        (%x::'b => 'a.
            (Ex::(('a => 'b) => bool) => bool)
             (%abs::'a => 'b.
                 (op &::bool => bool => bool)
                  ((All::('b => bool) => bool)
                    (%a::'b. (op =::'b => 'b => bool) (abs (x a)) a))
                  ((All::('a => bool) => bool)
                    (%r::'a.
                        (op =::bool => bool => bool) (P r)
                         ((op =::'a => 'a => bool) (x (abs r)) r)))))))"
  by (import bool ABS_REP_THM)

lemma LET_RAND: "(P::'b => bool) (Let (M::'a) (N::'a => 'b)) = (let x::'a = M in P (N x))"
  by (import bool LET_RAND)

lemma LET_RATOR: "Let (M::'a) (N::'a => 'b => 'c) (b::'b) = (let x::'a = M in N x b)"
  by (import bool LET_RATOR)

lemma SWAP_FORALL_THM: "ALL P. (ALL x. All (P x)) = (ALL y x. P x y)"
  by (import bool SWAP_FORALL_THM)

lemma SWAP_EXISTS_THM: "ALL P. (EX x. Ex (P x)) = (EX y x. P x y)"
  by (import bool SWAP_EXISTS_THM)

lemma AND_CONG: "ALL P P' Q Q'. (Q --> P = P') & (P' --> Q = Q') --> (P & Q) = (P' & Q')"
  by (import bool AND_CONG)

lemma OR_CONG: "ALL P P' Q Q'. (~ Q --> P = P') & (~ P' --> Q = Q') --> (P | Q) = (P' | Q')"
  by (import bool OR_CONG)

lemma COND_CONG: "ALL P Q x x' y y'.
   P = Q & (Q --> x = x') & (~ Q --> y = y') -->
   (if P then x else y) = (if Q then x' else y')"
  by (import bool COND_CONG)

lemma MONO_COND: "(x --> y) --> (z --> w) --> (if b then x else z) --> (if b then y else w)"
  by (import bool MONO_COND)

lemma SKOLEM_THM: "ALL P. (ALL x. Ex (P x)) = (EX f. ALL x. P x (f x))"
  by (import bool SKOLEM_THM)

lemma bool_case_thm: "(ALL (e0::'a) e1::'a. (case True of True => e0 | False => e1) = e0) &
(ALL (e0::'a) e1::'a. (case False of True => e0 | False => e1) = e1)"
  by (import bool bool_case_thm)

lemma bool_case_ID: "ALL x b. (case b of True => x | _ => x) = x"
  by (import bool bool_case_ID)

lemma boolAxiom: "ALL e0 e1. EX x. x True = e0 & x False = e1"
  by (import bool boolAxiom)

lemma UEXISTS_OR_THM: "ALL P Q. (EX! x. P x | Q x) --> Ex1 P | Ex1 Q"
  by (import bool UEXISTS_OR_THM)

lemma UEXISTS_SIMP: "(EX! x::'a. (t::bool)) = (t & (ALL x::'a. All (op = x)))"
  by (import bool UEXISTS_SIMP)

consts
  RES_ABSTRACT :: "('a => bool) => ('a => 'b) => 'a => 'b" 

specification (RES_ABSTRACT) RES_ABSTRACT_DEF: "(ALL (p::'a => bool) (m::'a => 'b) x::'a.
    IN x p --> RES_ABSTRACT p m x = m x) &
(ALL (p::'a => bool) (m1::'a => 'b) m2::'a => 'b.
    (ALL x::'a. IN x p --> m1 x = m2 x) -->
    RES_ABSTRACT p m1 = RES_ABSTRACT p m2)"
  by (import bool RES_ABSTRACT_DEF)

lemma BOOL_FUN_CASES_THM: "ALL f. f = (%b. True) | f = (%b. False) | f = (%b. b) | f = Not"
  by (import bool BOOL_FUN_CASES_THM)

lemma BOOL_FUN_INDUCT: "ALL P. P (%b. True) & P (%b. False) & P (%b. b) & P Not --> All P"
  by (import bool BOOL_FUN_INDUCT)

;end_setup

;setup_theory combin

constdefs
  K :: "'a => 'b => 'a" 
  "K == %x y. x"

lemma K_DEF: "K = (%x y. x)"
  by (import combin K_DEF)

constdefs
  S :: "('a => 'b => 'c) => ('a => 'b) => 'a => 'c" 
  "S == %f g x. f x (g x)"

lemma S_DEF: "S = (%f g x. f x (g x))"
  by (import combin S_DEF)

constdefs
  I :: "'a => 'a" 
  "(op ==::('a => 'a) => ('a => 'a) => prop) (I::'a => 'a)
 ((S::('a => ('a => 'a) => 'a) => ('a => 'a => 'a) => 'a => 'a)
   (K::'a => ('a => 'a) => 'a) (K::'a => 'a => 'a))"

lemma I_DEF: "(op =::('a => 'a) => ('a => 'a) => bool) (I::'a => 'a)
 ((S::('a => ('a => 'a) => 'a) => ('a => 'a => 'a) => 'a => 'a)
   (K::'a => ('a => 'a) => 'a) (K::'a => 'a => 'a))"
  by (import combin I_DEF)

constdefs
  C :: "('a => 'b => 'c) => 'b => 'a => 'c" 
  "C == %f x y. f y x"

lemma C_DEF: "C = (%f x y. f y x)"
  by (import combin C_DEF)

constdefs
  W :: "('a => 'a => 'b) => 'a => 'b" 
  "W == %f x. f x x"

lemma W_DEF: "W = (%f x. f x x)"
  by (import combin W_DEF)

lemma I_THM: "ALL x. I x = x"
  by (import combin I_THM)

lemma I_o_ID: "ALL f. I o f = f & f o I = f"
  by (import combin I_o_ID)

;end_setup

;setup_theory sum

lemma ISL_OR_ISR: "ALL x. ISL x | ISR x"
  by (import sum ISL_OR_ISR)

lemma INL: "ALL x. ISL x --> Inl (OUTL x) = x"
  by (import sum INL)

lemma INR: "ALL x. ISR x --> Inr (OUTR x) = x"
  by (import sum INR)

lemma sum_case_cong: "ALL (M::'b + 'c) (M'::'b + 'c) (f::'b => 'a) g::'c => 'a.
   M = M' &
   (ALL x::'b. M' = Inl x --> f x = (f'::'b => 'a) x) &
   (ALL y::'c. M' = Inr y --> g y = (g'::'c => 'a) y) -->
   sum_case f g M = sum_case f' g' M'"
  by (import sum sum_case_cong)

;end_setup

;setup_theory one

;end_setup

;setup_theory option

lemma option_CLAUSES: "(op &::bool => bool => bool)
 ((All::('a => bool) => bool)
   (%x::'a.
       (All::('a => bool) => bool)
        (%y::'a.
            (op =::bool => bool => bool)
             ((op =::'a option => 'a option => bool) ((Some::'a ~=> 'a) x)
               ((Some::'a ~=> 'a) y))
             ((op =::'a => 'a => bool) x y))))
 ((op &::bool => bool => bool)
   ((All::('a => bool) => bool)
     (%x::'a.
         (op =::'a => 'a => bool)
          ((the::'a option => 'a) ((Some::'a ~=> 'a) x)) x))
   ((op &::bool => bool => bool)
     ((All::('a => bool) => bool)
       (%x::'a.
           (Not::bool => bool)
            ((op =::'a option => 'a option => bool) (None::'a option)
              ((Some::'a ~=> 'a) x))))
     ((op &::bool => bool => bool)
       ((All::('a => bool) => bool)
         (%x::'a.
             (Not::bool => bool)
              ((op =::'a option => 'a option => bool) ((Some::'a ~=> 'a) x)
                (None::'a option))))
       ((op &::bool => bool => bool)
         ((All::('a => bool) => bool)
           (%x::'a.
               (op =::bool => bool => bool)
                ((IS_SOME::'a option => bool) ((Some::'a ~=> 'a) x))
                (True::bool)))
         ((op &::bool => bool => bool)
           ((op =::bool => bool => bool)
             ((IS_SOME::'a option => bool) (None::'a option)) (False::bool))
           ((op &::bool => bool => bool)
             ((All::('a option => bool) => bool)
               (%x::'a option.
                   (op =::bool => bool => bool)
                    ((IS_NONE::'a option => bool) x)
                    ((op =::'a option => 'a option => bool) x
                      (None::'a option))))
             ((op &::bool => bool => bool)
               ((All::('a option => bool) => bool)
                 (%x::'a option.
                     (op =::bool => bool => bool)
                      ((Not::bool => bool) ((IS_SOME::'a option => bool) x))
                      ((op =::'a option => 'a option => bool) x
                        (None::'a option))))
               ((op &::bool => bool => bool)
                 ((All::('a option => bool) => bool)
                   (%x::'a option.
                       (op -->::bool => bool => bool)
                        ((IS_SOME::'a option => bool) x)
                        ((op =::'a option => 'a option => bool)
                          ((Some::'a ~=> 'a) ((the::'a option => 'a) x))
                          x)))
                 ((op &::bool => bool => bool)
                   ((All::('a option => bool) => bool)
                     (%x::'a option.
                         (op =::'a option => 'a option => bool)
                          ((option_case::'a option
   => ('a ~=> 'a) => 'a option ~=> 'a)
                            (None::'a option) (Some::'a ~=> 'a) x)
                          x))
                   ((op &::bool => bool => bool)
                     ((All::('a option => bool) => bool)
                       (%x::'a option.
                           (op =::'a option => 'a option => bool)
                            ((option_case::'a option
     => ('a ~=> 'a) => 'a option ~=> 'a)
                              x (Some::'a ~=> 'a) x)
                            x))
                     ((op &::bool => bool => bool)
                       ((All::('a option => bool) => bool)
                         (%x::'a option.
                             (op -->::bool => bool => bool)
                              ((IS_NONE::'a option => bool) x)
                              ((op =::'b => 'b => bool)
                                ((option_case::'b
         => ('a => 'b) => 'a option => 'b)
                                  (e::'b) (f::'a => 'b) x)
                                e)))
                       ((op &::bool => bool => bool)
                         ((All::('a option => bool) => bool)
                           (%x::'a option.
                               (op -->::bool => bool => bool)
                                ((IS_SOME::'a option => bool) x)
                                ((op =::'b => 'b => bool)
                                  ((option_case::'b
           => ('a => 'b) => 'a option => 'b)
                                    e f x)
                                  (f ((the::'a option => 'a) x)))))
                         ((op &::bool => bool => bool)
                           ((All::('a option => bool) => bool)
                             (%x::'a option.
                                 (op -->::bool => bool => bool)
                                  ((IS_SOME::'a option => bool) x)
                                  ((op =::'a option => 'a option => bool)
                                    ((option_case::'a option
             => ('a ~=> 'a) => 'a option ~=> 'a)
(ea::'a option) (Some::'a ~=> 'a) x)
                                    x)))
                           ((op &::bool => bool => bool)
                             ((All::('b => bool) => bool)
                               (%u::'b.
                                   (All::(('a => 'b) => bool) => bool)
                                    (%f::'a => 'b.
  (op =::'b => 'b => bool)
   ((option_case::'b => ('a => 'b) => 'a option => 'b) u f
     (None::'a option))
   u)))
                             ((op &::bool => bool => bool)
                               ((All::('b => bool) => bool)
                                 (%u::'b.
                                     (All::(('a => 'b) => bool) => bool)
(%f::'a => 'b.
    (All::('a => bool) => bool)
     (%x::'a.
         (op =::'b => 'b => bool)
          ((option_case::'b => ('a => 'b) => 'a option => 'b) u f
            ((Some::'a ~=> 'a) x))
          (f x)))))
                               ((op &::bool => bool => bool)
                                 ((All::(('a => 'b) => bool) => bool)
                                   (%f::'a => 'b.
 (All::('a => bool) => bool)
  (%x::'a.
      (op =::'b option => 'b option => bool)
       ((option_map::('a => 'b) => 'a option ~=> 'b) f
         ((Some::'a ~=> 'a) x))
       ((Some::'b ~=> 'b) (f x)))))
                                 ((op &::bool => bool => bool)
                                   ((All::(('a => 'b) => bool) => bool)
                                     (%f::'a => 'b.
   (op =::'b option => 'b option => bool)
    ((option_map::('a => 'b) => 'a option ~=> 'b) f (None::'a option))
    (None::'b option)))
                                   ((op &::bool => bool => bool)
                                     ((op =::'a option => 'a option => bool)
 ((OPTION_JOIN::'a option option ~=> 'a) (None::'a option option))
 (None::'a option))
                                     ((All::('a option => bool) => bool)
 (%x::'a option.
     (op =::'a option => 'a option => bool)
      ((OPTION_JOIN::'a option option ~=> 'a)
        ((Some::'a option ~=> 'a option) x))
      x))))))))))))))))))))"
  by (import option option_CLAUSES)

lemma option_case_compute: "option_case (e::'b) (f::'a => 'b) (x::'a option) =
(if IS_SOME x then f (the x) else e)"
  by (import option option_case_compute)

lemma OPTION_MAP_EQ_SOME: "ALL f x y. (option_map f x = Some y) = (EX z. x = Some z & y = f z)"
  by (import option OPTION_MAP_EQ_SOME)

lemma OPTION_JOIN_EQ_SOME: "ALL x xa. (OPTION_JOIN x = Some xa) = (x = Some (Some xa))"
  by (import option OPTION_JOIN_EQ_SOME)

lemma option_case_cong: "ALL M M' u f.
   M = M' & (M' = None --> u = u') & (ALL x. M' = Some x --> f x = f' x) -->
   option_case u f M = option_case u' f' M'"
  by (import option option_case_cong)

;end_setup

;setup_theory marker

consts
  stmarker :: "'a => 'a" 

defs
  stmarker_primdef: "stmarker == %x. x"

lemma stmarker_def: "ALL x. stmarker x = x"
  by (import marker stmarker_def)

lemma move_left_conj: "ALL x xa xb.
   (x & stmarker xb) = (stmarker xb & x) &
   ((stmarker xb & x) & xa) = (stmarker xb & x & xa) &
   (x & stmarker xb & xa) = (stmarker xb & x & xa)"
  by (import marker move_left_conj)

lemma move_right_conj: "ALL x xa xb.
   (stmarker xb & x) = (x & stmarker xb) &
   (x & xa & stmarker xb) = ((x & xa) & stmarker xb) &
   ((x & stmarker xb) & xa) = ((x & xa) & stmarker xb)"
  by (import marker move_right_conj)

lemma move_left_disj: "ALL x xa xb.
   (x | stmarker xb) = (stmarker xb | x) &
   ((stmarker xb | x) | xa) = (stmarker xb | x | xa) &
   (x | stmarker xb | xa) = (stmarker xb | x | xa)"
  by (import marker move_left_disj)

lemma move_right_disj: "ALL x xa xb.
   (stmarker xb | x) = (x | stmarker xb) &
   (x | xa | stmarker xb) = ((x | xa) | stmarker xb) &
   ((x | stmarker xb) | xa) = ((x | xa) | stmarker xb)"
  by (import marker move_right_disj)

;end_setup

;setup_theory relation

constdefs
  TC :: "('a => 'a => bool) => 'a => 'a => bool" 
  "TC ==
%R a b.
   ALL P.
      (ALL x y. R x y --> P x y) & (ALL x y z. P x y & P y z --> P x z) -->
      P a b"

lemma TC_DEF: "ALL R a b.
   TC R a b =
   (ALL P.
       (ALL x y. R x y --> P x y) & (ALL x y z. P x y & P y z --> P x z) -->
       P a b)"
  by (import relation TC_DEF)

constdefs
  RTC :: "('a => 'a => bool) => 'a => 'a => bool" 
  "RTC ==
%R a b.
   ALL P. (ALL x. P x x) & (ALL x y z. R x y & P y z --> P x z) --> P a b"

lemma RTC_DEF: "ALL R a b.
   RTC R a b =
   (ALL P. (ALL x. P x x) & (ALL x y z. R x y & P y z --> P x z) --> P a b)"
  by (import relation RTC_DEF)

consts
  RC :: "('a => 'a => bool) => 'a => 'a => bool" 

defs
  RC_primdef: "RC == %R x y. x = y | R x y"

lemma RC_def: "ALL R x y. RC R x y = (x = y | R x y)"
  by (import relation RC_def)

consts
  transitive :: "('a => 'a => bool) => bool" 

defs
  transitive_primdef: "transitive == %R. ALL x y z. R x y & R y z --> R x z"

lemma transitive_def: "ALL R. transitive R = (ALL x y z. R x y & R y z --> R x z)"
  by (import relation transitive_def)

constdefs
  pred_reflexive :: "('a => 'a => bool) => bool" 
  "pred_reflexive == %R. ALL x. R x x"

lemma reflexive_def: "ALL R. pred_reflexive R = (ALL x. R x x)"
  by (import relation reflexive_def)

lemma TC_TRANSITIVE: "ALL x. transitive (TC x)"
  by (import relation TC_TRANSITIVE)

lemma RTC_INDUCT: "ALL x xa.
   (ALL x. xa x x) & (ALL xb y z. x xb y & xa y z --> xa xb z) -->
   (ALL xb xc. RTC x xb xc --> xa xb xc)"
  by (import relation RTC_INDUCT)

lemma TC_RULES: "ALL x.
   (ALL xa xb. x xa xb --> TC x xa xb) &
   (ALL xa xb xc. TC x xa xb & TC x xb xc --> TC x xa xc)"
  by (import relation TC_RULES)

lemma RTC_RULES: "ALL x.
   (ALL xa. RTC x xa xa) &
   (ALL xa xb xc. x xa xb & RTC x xb xc --> RTC x xa xc)"
  by (import relation RTC_RULES)

lemma RTC_STRONG_INDUCT: "ALL R P.
   (ALL x. P x x) & (ALL x y z. R x y & RTC R y z & P y z --> P x z) -->
   (ALL x y. RTC R x y --> P x y)"
  by (import relation RTC_STRONG_INDUCT)

lemma RTC_RTC: "ALL R x y. RTC R x y --> (ALL z. RTC R y z --> RTC R x z)"
  by (import relation RTC_RTC)

lemma RTC_TRANSITIVE: "ALL x. transitive (RTC x)"
  by (import relation RTC_TRANSITIVE)

lemma RTC_REFLEXIVE: "ALL R. pred_reflexive (RTC R)"
  by (import relation RTC_REFLEXIVE)

lemma RC_REFLEXIVE: "ALL R. pred_reflexive (RC R)"
  by (import relation RC_REFLEXIVE)

lemma TC_SUBSET: "ALL x xa xb. x xa xb --> TC x xa xb"
  by (import relation TC_SUBSET)

lemma RTC_SUBSET: "ALL R x y. R x y --> RTC R x y"
  by (import relation RTC_SUBSET)

lemma RC_SUBSET: "ALL R x y. R x y --> RC R x y"
  by (import relation RC_SUBSET)

lemma RC_RTC: "ALL R x y. RC R x y --> RTC R x y"
  by (import relation RC_RTC)

lemma TC_INDUCT: "ALL x xa.
   (ALL xb y. x xb y --> xa xb y) &
   (ALL x y z. xa x y & xa y z --> xa x z) -->
   (ALL xb xc. TC x xb xc --> xa xb xc)"
  by (import relation TC_INDUCT)

lemma TC_INDUCT_LEFT1: "ALL x xa.
   (ALL xb y. x xb y --> xa xb y) &
   (ALL xb y z. x xb y & xa y z --> xa xb z) -->
   (ALL xb xc. TC x xb xc --> xa xb xc)"
  by (import relation TC_INDUCT_LEFT1)

lemma TC_STRONG_INDUCT: "ALL R P.
   (ALL x y. R x y --> P x y) &
   (ALL x y z. P x y & P y z & TC R x y & TC R y z --> P x z) -->
   (ALL u v. TC R u v --> P u v)"
  by (import relation TC_STRONG_INDUCT)

lemma TC_STRONG_INDUCT_LEFT1: "ALL R P.
   (ALL x y. R x y --> P x y) &
   (ALL x y z. R x y & P y z & TC R y z --> P x z) -->
   (ALL u v. TC R u v --> P u v)"
  by (import relation TC_STRONG_INDUCT_LEFT1)

lemma TC_RTC: "ALL R x y. TC R x y --> RTC R x y"
  by (import relation TC_RTC)

lemma RTC_TC_RC: "ALL R x y. RTC R x y --> RC R x y | TC R x y"
  by (import relation RTC_TC_RC)

lemma TC_RC_EQNS: "ALL R. RC (TC R) = RTC R & TC (RC R) = RTC R"
  by (import relation TC_RC_EQNS)

lemma RC_IDEM: "ALL R. RC (RC R) = RC R"
  by (import relation RC_IDEM)

lemma TC_IDEM: "ALL R. TC (TC R) = TC R"
  by (import relation TC_IDEM)

lemma RTC_IDEM: "ALL R. RTC (RTC R) = RTC R"
  by (import relation RTC_IDEM)

lemma RTC_CASES1: "ALL x xa xb. RTC x xa xb = (xa = xb | (EX u. x xa u & RTC x u xb))"
  by (import relation RTC_CASES1)

lemma RTC_CASES2: "ALL x xa xb. RTC x xa xb = (xa = xb | (EX u. RTC x xa u & x u xb))"
  by (import relation RTC_CASES2)

lemma RTC_CASES_RTC_TWICE: "ALL x xa xb. RTC x xa xb = (EX u. RTC x xa u & RTC x u xb)"
  by (import relation RTC_CASES_RTC_TWICE)

lemma TC_CASES1: "ALL R x z. TC R x z --> R x z | (EX y. R x y & TC R y z)"
  by (import relation TC_CASES1)

lemma TC_CASES2: "ALL R x z. TC R x z --> R x z | (EX y. TC R x y & R y z)"
  by (import relation TC_CASES2)

lemma TC_MONOTONE: "ALL R Q. (ALL x y. R x y --> Q x y) --> (ALL x y. TC R x y --> TC Q x y)"
  by (import relation TC_MONOTONE)

lemma RTC_MONOTONE: "ALL R Q. (ALL x y. R x y --> Q x y) --> (ALL x y. RTC R x y --> RTC Q x y)"
  by (import relation RTC_MONOTONE)

constdefs
  WF :: "('a => 'a => bool) => bool" 
  "WF == %R. ALL B. Ex B --> (EX min. B min & (ALL b. R b min --> ~ B b))"

lemma WF_DEF: "ALL R. WF R = (ALL B. Ex B --> (EX min. B min & (ALL b. R b min --> ~ B b)))"
  by (import relation WF_DEF)

lemma WF_INDUCTION_THM: "ALL R. WF R --> (ALL P. (ALL x. (ALL y. R y x --> P y) --> P x) --> All P)"
  by (import relation WF_INDUCTION_THM)

lemma WF_NOT_REFL: "ALL x xa xb. WF x --> x xa xb --> xa ~= xb"
  by (import relation WF_NOT_REFL)

constdefs
  EMPTY_REL :: "'a => 'a => bool" 
  "EMPTY_REL == %x y. False"

lemma EMPTY_REL_DEF: "ALL x y. EMPTY_REL x y = False"
  by (import relation EMPTY_REL_DEF)

lemma WF_EMPTY_REL: "WF EMPTY_REL"
  by (import relation WF_EMPTY_REL)

lemma WF_SUBSET: "ALL x xa. WF x & (ALL xb y. xa xb y --> x xb y) --> WF xa"
  by (import relation WF_SUBSET)

lemma WF_TC: "ALL R. WF R --> WF (TC R)"
  by (import relation WF_TC)

consts
  inv_image :: "('b => 'b => bool) => ('a => 'b) => 'a => 'a => bool" 

defs
  inv_image_primdef: "relation.inv_image ==
%(R::'b => 'b => bool) (f::'a => 'b) (x::'a) y::'a. R (f x) (f y)"

lemma inv_image_def: "ALL (R::'b => 'b => bool) f::'a => 'b.
   relation.inv_image R f = (%(x::'a) y::'a. R (f x) (f y))"
  by (import relation inv_image_def)

lemma WF_inv_image: "ALL (R::'b => 'b => bool) f::'a => 'b. WF R --> WF (relation.inv_image R f)"
  by (import relation WF_inv_image)

constdefs
  RESTRICT :: "('a => 'b) => ('a => 'a => bool) => 'a => 'a => 'b" 
  "RESTRICT == %f R x y. if R y x then f y else ARB"

lemma RESTRICT_DEF: "ALL f R x. RESTRICT f R x = (%y. if R y x then f y else ARB)"
  by (import relation RESTRICT_DEF)

lemma RESTRICT_LEMMA: "ALL x xa xb xc. xa xb xc --> RESTRICT x xa xc xb = x xb"
  by (import relation RESTRICT_LEMMA)

consts
  approx :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => ('a => 'b) => bool" 

defs
  approx_primdef: "approx == %R M x f. f = RESTRICT (%y. M (RESTRICT f R y) y) R x"

lemma approx_def: "ALL R M x f. approx R M x f = (f = RESTRICT (%y. M (RESTRICT f R y) y) R x)"
  by (import relation approx_def)

consts
  the_fun :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => 'a => 'b" 

defs
  the_fun_primdef: "the_fun == %R M x. Eps (approx R M x)"

lemma the_fun_def: "ALL R M x. the_fun R M x = Eps (approx R M x)"
  by (import relation the_fun_def)

constdefs
  WFREC :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => 'b" 
  "WFREC ==
%R M x. M (RESTRICT (the_fun (TC R) (%f v. M (RESTRICT f R v) v) x) R x) x"

lemma WFREC_DEF: "ALL R M.
   WFREC R M =
   (%x. M (RESTRICT (the_fun (TC R) (%f v. M (RESTRICT f R v) v) x) R x) x)"
  by (import relation WFREC_DEF)

lemma WFREC_THM: "ALL R M. WF R --> (ALL x. WFREC R M x = M (RESTRICT (WFREC R M) R x) x)"
  by (import relation WFREC_THM)

lemma WFREC_COROLLARY: "ALL M R f. f = WFREC R M --> WF R --> (ALL x. f x = M (RESTRICT f R x) x)"
  by (import relation WFREC_COROLLARY)

lemma WF_RECURSION_THM: "ALL R. WF R --> (ALL M. EX! f. ALL x. f x = M (RESTRICT f R x) x)"
  by (import relation WF_RECURSION_THM)

;end_setup

;setup_theory pair

lemma CURRY_ONE_ONE_THM: "(curry f = curry g) = (f = g)"
  by (import pair CURRY_ONE_ONE_THM)

lemma UNCURRY_ONE_ONE_THM: "(split f = split g) = (f = g)"
  by (import pair UNCURRY_ONE_ONE_THM)

lemma pair_Axiom: "ALL f. EX x. ALL xa y. x (xa, y) = f xa y"
  by (import pair pair_Axiom)

lemma UNCURRY_CONG: "ALL M M' f.
   M = M' & (ALL x y. M' = (x, y) --> f x y = f' x y) -->
   split f M = split f' M'"
  by (import pair UNCURRY_CONG)

lemma ELIM_PEXISTS: "(EX p. P (fst p) (snd p)) = (EX p1. Ex (P p1))"
  by (import pair ELIM_PEXISTS)

lemma ELIM_PFORALL: "(ALL p. P (fst p) (snd p)) = (ALL p1. All (P p1))"
  by (import pair ELIM_PFORALL)

lemma PFORALL_THM: "ALL x. (ALL xa. All (x xa)) = All (split x)"
  by (import pair PFORALL_THM)

lemma PEXISTS_THM: "ALL x. (EX xa. Ex (x xa)) = Ex (split x)"
  by (import pair PEXISTS_THM)

lemma LET2_RAND: "ALL (x::'c => 'd) (xa::'a * 'b) xb::'a => 'b => 'c.
   x (Let xa (split xb)) = (let (xa::'a, y::'b) = xa in x (xb xa y))"
  by (import pair LET2_RAND)

lemma LET2_RATOR: "ALL (x::'a1 * 'a2) (xa::'a1 => 'a2 => 'b => 'c) xb::'b.
   Let x (split xa) xb = (let (x::'a1, y::'a2) = x in xa x y xb)"
  by (import pair LET2_RATOR)

lemma pair_case_cong: "ALL x xa xb.
   x = xa & (ALL x y. xa = (x, y) --> xb x y = f' x y) -->
   split xb x = split f' xa"
  by (import pair pair_case_cong)

constdefs
  LEX :: "('a => 'a => bool) => ('b => 'b => bool) => 'a * 'b => 'a * 'b => bool" 
  "LEX == %R1 R2 (s, t) (u, v). R1 s u | s = u & R2 t v"

lemma LEX_DEF: "ALL R1 R2. LEX R1 R2 = (%(s, t) (u, v). R1 s u | s = u & R2 t v)"
  by (import pair LEX_DEF)

lemma WF_LEX: "ALL x xa. WF x & WF xa --> WF (LEX x xa)"
  by (import pair WF_LEX)

constdefs
  RPROD :: "('a => 'a => bool) => ('b => 'b => bool) => 'a * 'b => 'a * 'b => bool" 
  "RPROD == %R1 R2 (s, t) (u, v). R1 s u & R2 t v"

lemma RPROD_DEF: "ALL R1 R2. RPROD R1 R2 = (%(s, t) (u, v). R1 s u & R2 t v)"
  by (import pair RPROD_DEF)

lemma WF_RPROD: "ALL R Q. WF R & WF Q --> WF (RPROD R Q)"
  by (import pair WF_RPROD)

;end_setup

;setup_theory num

;end_setup

;setup_theory prim_rec

lemma LESS_0_0: "0 < Suc 0"
  by (import prim_rec LESS_0_0)

lemma LESS_LEMMA1: "ALL x xa. x < Suc xa --> x = xa | x < xa"
  by (import prim_rec LESS_LEMMA1)

lemma LESS_LEMMA2: "ALL m n. m = n | m < n --> m < Suc n"
  by (import prim_rec LESS_LEMMA2)

lemma LESS_THM: "ALL m n. (m < Suc n) = (m = n | m < n)"
  by (import prim_rec LESS_THM)

lemma LESS_SUC_IMP: "ALL x xa. x < Suc xa --> x ~= xa --> x < xa"
  by (import prim_rec LESS_SUC_IMP)

lemma EQ_LESS: "ALL n. Suc m = n --> m < n"
  by (import prim_rec EQ_LESS)

lemma NOT_LESS_EQ: "ALL (m::nat) n::nat. m = n --> ~ m < n"
  by (import prim_rec NOT_LESS_EQ)

constdefs
  SIMP_REC_REL :: "(nat => 'a) => 'a => ('a => 'a) => nat => bool" 
  "(op ==::((nat => 'a) => 'a => ('a => 'a) => nat => bool)
        => ((nat => 'a) => 'a => ('a => 'a) => nat => bool) => prop)
 (SIMP_REC_REL::(nat => 'a) => 'a => ('a => 'a) => nat => bool)
 (%(fun::nat => 'a) (x::'a) (f::'a => 'a) n::nat.
     (op &::bool => bool => bool)
      ((op =::'a => 'a => bool) (fun (0::nat)) x)
      ((All::(nat => bool) => bool)
        (%m::nat.
            (op -->::bool => bool => bool) ((op <::nat => nat => bool) m n)
             ((op =::'a => 'a => bool) (fun ((Suc::nat => nat) m))
               (f (fun m))))))"

lemma SIMP_REC_REL: "(All::((nat => 'a) => bool) => bool)
 (%fun::nat => 'a.
     (All::('a => bool) => bool)
      (%x::'a.
          (All::(('a => 'a) => bool) => bool)
           (%f::'a => 'a.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (op =::bool => bool => bool)
                     ((SIMP_REC_REL::(nat => 'a)
                                     => 'a => ('a => 'a) => nat => bool)
                       fun x f n)
                     ((op &::bool => bool => bool)
                       ((op =::'a => 'a => bool) (fun (0::nat)) x)
                       ((All::(nat => bool) => bool)
                         (%m::nat.
                             (op -->::bool => bool => bool)
                              ((op <::nat => nat => bool) m n)
                              ((op =::'a => 'a => bool)
                                (fun ((Suc::nat => nat) m))
                                (f (fun m))))))))))"
  by (import prim_rec SIMP_REC_REL)

lemma SIMP_REC_EXISTS: "ALL x f n. EX fun. SIMP_REC_REL fun x f n"
  by (import prim_rec SIMP_REC_EXISTS)

lemma SIMP_REC_REL_UNIQUE: "ALL x xa xb xc xd xe.
   SIMP_REC_REL xb x xa xd & SIMP_REC_REL xc x xa xe -->
   (ALL n. n < xd & n < xe --> xb n = xc n)"
  by (import prim_rec SIMP_REC_REL_UNIQUE)

lemma SIMP_REC_REL_UNIQUE_RESULT: "ALL x f n. EX! y. EX g. SIMP_REC_REL g x f (Suc n) & y = g n"
  by (import prim_rec SIMP_REC_REL_UNIQUE_RESULT)

consts
  SIMP_REC :: "'a => ('a => 'a) => nat => 'a" 

specification (SIMP_REC) SIMP_REC: "ALL x f' n. EX g. SIMP_REC_REL g x f' (Suc n) & SIMP_REC x f' n = g n"
  by (import prim_rec SIMP_REC)

lemma LESS_SUC_SUC: "ALL m. m < Suc m & m < Suc (Suc m)"
  by (import prim_rec LESS_SUC_SUC)

lemma SIMP_REC_THM: "ALL x f.
   SIMP_REC x f 0 = x & (ALL m. SIMP_REC x f (Suc m) = f (SIMP_REC x f m))"
  by (import prim_rec SIMP_REC_THM)

constdefs
  PRE :: "nat => nat" 
  "PRE == %m. if m = 0 then 0 else SOME n. m = Suc n"

lemma PRE_DEF: "ALL m. PRE m = (if m = 0 then 0 else SOME n. m = Suc n)"
  by (import prim_rec PRE_DEF)

lemma PRE: "PRE 0 = 0 & (ALL m. PRE (Suc m) = m)"
  by (import prim_rec PRE)

constdefs
  PRIM_REC_FUN :: "'a => ('a => nat => 'a) => nat => nat => 'a" 
  "PRIM_REC_FUN == %x f. SIMP_REC (%n. x) (%fun n. f (fun (PRE n)) n)"

lemma PRIM_REC_FUN: "ALL x f. PRIM_REC_FUN x f = SIMP_REC (%n. x) (%fun n. f (fun (PRE n)) n)"
  by (import prim_rec PRIM_REC_FUN)

lemma PRIM_REC_EQN: "ALL x f.
   (ALL n. PRIM_REC_FUN x f 0 n = x) &
   (ALL m n. PRIM_REC_FUN x f (Suc m) n = f (PRIM_REC_FUN x f m (PRE n)) n)"
  by (import prim_rec PRIM_REC_EQN)

constdefs
  PRIM_REC :: "'a => ('a => nat => 'a) => nat => 'a" 
  "PRIM_REC == %x f m. PRIM_REC_FUN x f m (PRE m)"

lemma PRIM_REC: "ALL x f m. PRIM_REC x f m = PRIM_REC_FUN x f m (PRE m)"
  by (import prim_rec PRIM_REC)

lemma PRIM_REC_THM: "ALL x f.
   PRIM_REC x f 0 = x & (ALL m. PRIM_REC x f (Suc m) = f (PRIM_REC x f m) m)"
  by (import prim_rec PRIM_REC_THM)

lemma DC: "ALL P R a.
   P a & (ALL x. P x --> (EX y. P y & R x y)) -->
   (EX x. x 0 = a & (ALL n. P (x n) & R (x n) (x (Suc n))))"
  by (import prim_rec DC)

lemma num_Axiom_old: "ALL e f. EX! fn1. fn1 0 = e & (ALL n. fn1 (Suc n) = f (fn1 n) n)"
  by (import prim_rec num_Axiom_old)

lemma num_Axiom: "ALL e f. EX x. x 0 = e & (ALL n. x (Suc n) = f n (x n))"
  by (import prim_rec num_Axiom)

consts
  wellfounded :: "('a => 'a => bool) => bool" 

defs
  wellfounded_primdef: "wellfounded == %R. ~ (EX f. ALL n. R (f (Suc n)) (f n))"

lemma wellfounded_def: "ALL R. wellfounded R = (~ (EX f. ALL n. R (f (Suc n)) (f n)))"
  by (import prim_rec wellfounded_def)

lemma WF_IFF_WELLFOUNDED: "ALL R. WF R = wellfounded R"
  by (import prim_rec WF_IFF_WELLFOUNDED)

lemma WF_PRED: "WF (%x y. y = Suc x)"
  by (import prim_rec WF_PRED)

lemma WF_LESS: "(WF::(nat => nat => bool) => bool) (op <::nat => nat => bool)"
  by (import prim_rec WF_LESS)

consts
  measure :: "('a => nat) => 'a => 'a => bool" 

defs
  measure_primdef: "prim_rec.measure == relation.inv_image op <"

lemma measure_def: "prim_rec.measure = relation.inv_image op <"
  by (import prim_rec measure_def)

lemma WF_measure: "ALL x. WF (prim_rec.measure x)"
  by (import prim_rec WF_measure)

lemma measure_thm: "ALL x xa xb. prim_rec.measure x xa xb = (x xa < x xb)"
  by (import prim_rec measure_thm)

;end_setup

;setup_theory arithmetic

constdefs
  nat_elim__magic :: "nat => nat" 
  "nat_elim__magic == %n. n"

lemma nat_elim__magic: "ALL n. nat_elim__magic n = n"
  by (import arithmetic nat_elim__magic)

consts
  EVEN :: "nat => bool" 

specification (EVEN) EVEN: "EVEN 0 = True & (ALL n. EVEN (Suc n) = (~ EVEN n))"
  by (import arithmetic EVEN)

consts
  ODD :: "nat => bool" 

specification (ODD) ODD: "ODD 0 = False & (ALL n. ODD (Suc n) = (~ ODD n))"
  by (import arithmetic ODD)

lemma TWO: "2 = Suc 1"
  by (import arithmetic TWO)

lemma NORM_0: "(0::nat) = (0::nat)"
  by (import arithmetic NORM_0)

lemma num_case_compute: "ALL n. nat_case f g n = (if n = 0 then f else g (PRE n))"
  by (import arithmetic num_case_compute)

lemma ADD_CLAUSES: "0 + m = m & m + 0 = m & Suc m + n = Suc (m + n) & m + Suc n = Suc (m + n)"
  by (import arithmetic ADD_CLAUSES)

lemma LESS_ADD: "ALL (m::nat) n::nat. n < m --> (EX p::nat. p + n = m)"
  by (import arithmetic LESS_ADD)

lemma LESS_ANTISYM: "ALL (m::nat) n::nat. ~ (m < n & n < m)"
  by (import arithmetic LESS_ANTISYM)

lemma LESS_LESS_SUC: "ALL x xa. ~ (x < xa & xa < Suc x)"
  by (import arithmetic LESS_LESS_SUC)

lemma FUN_EQ_LEMMA: "ALL f x1 x2. f x1 & ~ f x2 --> x1 ~= x2"
  by (import arithmetic FUN_EQ_LEMMA)

lemma LESS_NOT_SUC: "ALL m n. m < n & n ~= Suc m --> Suc m < n"
  by (import arithmetic LESS_NOT_SUC)

lemma LESS_0_CASES: "ALL m::nat. (0::nat) = m | (0::nat) < m"
  by (import arithmetic LESS_0_CASES)

lemma LESS_CASES_IMP: "ALL (m::nat) n::nat. ~ m < n & m ~= n --> n < m"
  by (import arithmetic LESS_CASES_IMP)

lemma LESS_CASES: "ALL (m::nat) n::nat. m < n | n <= m"
  by (import arithmetic LESS_CASES)

lemma LESS_EQ_SUC_REFL: "ALL m. m <= Suc m"
  by (import arithmetic LESS_EQ_SUC_REFL)

lemma LESS_ADD_NONZERO: "ALL (m::nat) n::nat. n ~= (0::nat) --> m < m + n"
  by (import arithmetic LESS_ADD_NONZERO)

lemma LESS_EQ_ANTISYM: "ALL (x::nat) xa::nat. ~ (x < xa & xa <= x)"
  by (import arithmetic LESS_EQ_ANTISYM)

lemma SUB_0: "ALL m::nat. (0::nat) - m = (0::nat) & m - (0::nat) = m"
  by (import arithmetic SUB_0)

lemma SUC_SUB1: "ALL m. Suc m - 1 = m"
  by (import arithmetic SUC_SUB1)

lemma PRE_SUB1: "ALL m. PRE m = m - 1"
  by (import arithmetic PRE_SUB1)

lemma MULT_CLAUSES: "ALL x xa.
   0 * x = 0 &
   x * 0 = 0 &
   1 * x = x &
   x * 1 = x & Suc x * xa = x * xa + xa & x * Suc xa = x + x * xa"
  by (import arithmetic MULT_CLAUSES)

lemma PRE_SUB: "ALL m n. PRE (m - n) = PRE m - n"
  by (import arithmetic PRE_SUB)

lemma ADD_EQ_1: "ALL (m::nat) n::nat.
   (m + n = (1::nat)) =
   (m = (1::nat) & n = (0::nat) | m = (0::nat) & n = (1::nat))"
  by (import arithmetic ADD_EQ_1)

lemma ADD_INV_0_EQ: "ALL (m::nat) n::nat. (m + n = m) = (n = (0::nat))"
  by (import arithmetic ADD_INV_0_EQ)

lemma PRE_SUC_EQ: "ALL m n. 0 < n --> (m = PRE n) = (Suc m = n)"
  by (import arithmetic PRE_SUC_EQ)

lemma INV_PRE_EQ: "ALL m n. 0 < m & 0 < n --> (PRE m = PRE n) = (m = n)"
  by (import arithmetic INV_PRE_EQ)

lemma LESS_SUC_NOT: "ALL m n. m < n --> ~ n < Suc m"
  by (import arithmetic LESS_SUC_NOT)

lemma ADD_EQ_SUB: "ALL (m::nat) (n::nat) p::nat. n <= p --> (m + n = p) = (m = p - n)"
  by (import arithmetic ADD_EQ_SUB)

lemma LESS_ADD_1: "ALL (x::nat) xa::nat. xa < x --> (EX xb::nat. x = xa + (xb + (1::nat)))"
  by (import arithmetic LESS_ADD_1)

lemma NOT_ODD_EQ_EVEN: "ALL n m. Suc (n + n) ~= m + m"
  by (import arithmetic NOT_ODD_EQ_EVEN)

lemma MULT_SUC_EQ: "ALL p m n. (n * Suc p = m * Suc p) = (n = m)"
  by (import arithmetic MULT_SUC_EQ)

lemma MULT_EXP_MONO: "ALL p q n m. (n * Suc q ^ p = m * Suc q ^ p) = (n = m)"
  by (import arithmetic MULT_EXP_MONO)

lemma LESS_ADD_SUC: "ALL m n. m < m + Suc n"
  by (import arithmetic LESS_ADD_SUC)

lemma LESS_OR_EQ_ADD: "ALL (n::nat) m::nat. n < m | (EX p::nat. n = p + m)"
  by (import arithmetic LESS_OR_EQ_ADD)

lemma WOP: "(All::((nat => bool) => bool) => bool)
 (%P::nat => bool.
     (op -->::bool => bool => bool) ((Ex::(nat => bool) => bool) P)
      ((Ex::(nat => bool) => bool)
        (%n::nat.
            (op &::bool => bool => bool) (P n)
             ((All::(nat => bool) => bool)
               (%m::nat.
                   (op -->::bool => bool => bool)
                    ((op <::nat => nat => bool) m n)
                    ((Not::bool => bool) (P m)))))))"
  by (import arithmetic WOP)

lemma INV_PRE_LESS: "ALL m. 0 < m --> (ALL n. (PRE m < PRE n) = (m < n))"
  by (import arithmetic INV_PRE_LESS)

lemma INV_PRE_LESS_EQ: "ALL n. 0 < n --> (ALL m. (PRE m <= PRE n) = (m <= n))"
  by (import arithmetic INV_PRE_LESS_EQ)

lemma SUB_EQ_EQ_0: "ALL (m::nat) n::nat. (m - n = m) = (m = (0::nat) | n = (0::nat))"
  by (import arithmetic SUB_EQ_EQ_0)

lemma SUB_LESS_OR: "ALL (m::nat) n::nat. n < m --> n <= m - (1::nat)"
  by (import arithmetic SUB_LESS_OR)

lemma LESS_SUB_ADD_LESS: "ALL (n::nat) (m::nat) i::nat. i < n - m --> i + m < n"
  by (import arithmetic LESS_SUB_ADD_LESS)

lemma LESS_EQ_SUB_LESS: "ALL (x::nat) xa::nat. xa <= x --> (ALL c::nat. (x - xa < c) = (x < xa + c))"
  by (import arithmetic LESS_EQ_SUB_LESS)

lemma NOT_SUC_LESS_EQ: "ALL x xa. (~ Suc x <= xa) = (xa <= x)"
  by (import arithmetic NOT_SUC_LESS_EQ)

lemma SUB_LESS_EQ_ADD: "ALL (m::nat) p::nat. m <= p --> (ALL n::nat. (p - m <= n) = (p <= m + n))"
  by (import arithmetic SUB_LESS_EQ_ADD)

lemma SUB_CANCEL: "ALL (x::nat) (xa::nat) xb::nat.
   xa <= x & xb <= x --> (x - xa = x - xb) = (xa = xb)"
  by (import arithmetic SUB_CANCEL)

lemma NOT_EXP_0: "ALL m n. Suc n ^ m ~= 0"
  by (import arithmetic NOT_EXP_0)

lemma ZERO_LESS_EXP: "ALL m n. 0 < Suc n ^ m"
  by (import arithmetic ZERO_LESS_EXP)

lemma ODD_OR_EVEN: "ALL x. EX xa. x = Suc (Suc 0) * xa | x = Suc (Suc 0) * xa + 1"
  by (import arithmetic ODD_OR_EVEN)

lemma LESS_EXP_SUC_MONO: "ALL n m. Suc (Suc m) ^ n < Suc (Suc m) ^ Suc n"
  by (import arithmetic LESS_EXP_SUC_MONO)

lemma LESS_LESS_CASES: "ALL (m::nat) n::nat. m = n | m < n | n < m"
  by (import arithmetic LESS_LESS_CASES)

lemma LESS_EQUAL_ADD: "ALL (m::nat) n::nat. m <= n --> (EX p::nat. n = m + p)"
  by (import arithmetic LESS_EQUAL_ADD)

lemma LESS_EQ_EXISTS: "ALL (m::nat) n::nat. (m <= n) = (EX p::nat. n = m + p)"
  by (import arithmetic LESS_EQ_EXISTS)

lemma MULT_EQ_1: "ALL (x::nat) y::nat. (x * y = (1::nat)) = (x = (1::nat) & y = (1::nat))"
  by (import arithmetic MULT_EQ_1)

consts
  FACT :: "nat => nat" 

specification (FACT) FACT: "FACT 0 = 1 & (ALL n. FACT (Suc n) = Suc n * FACT n)"
  by (import arithmetic FACT)

lemma FACT_LESS: "ALL n. 0 < FACT n"
  by (import arithmetic FACT_LESS)

lemma EVEN_ODD: "ALL n. EVEN n = (~ ODD n)"
  by (import arithmetic EVEN_ODD)

lemma ODD_EVEN: "ALL x. ODD x = (~ EVEN x)"
  by (import arithmetic ODD_EVEN)

lemma EVEN_OR_ODD: "ALL x. EVEN x | ODD x"
  by (import arithmetic EVEN_OR_ODD)

lemma EVEN_AND_ODD: "ALL x. ~ (EVEN x & ODD x)"
  by (import arithmetic EVEN_AND_ODD)

lemma EVEN_ADD: "ALL m n. EVEN (m + n) = (EVEN m = EVEN n)"
  by (import arithmetic EVEN_ADD)

lemma EVEN_MULT: "ALL m n. EVEN (m * n) = (EVEN m | EVEN n)"
  by (import arithmetic EVEN_MULT)

lemma ODD_ADD: "ALL m n. ODD (m + n) = (ODD m ~= ODD n)"
  by (import arithmetic ODD_ADD)

lemma ODD_MULT: "ALL m n. ODD (m * n) = (ODD m & ODD n)"
  by (import arithmetic ODD_MULT)

lemma EVEN_DOUBLE: "ALL n. EVEN (2 * n)"
  by (import arithmetic EVEN_DOUBLE)

lemma ODD_DOUBLE: "ALL x. ODD (Suc (2 * x))"
  by (import arithmetic ODD_DOUBLE)

lemma EVEN_ODD_EXISTS: "ALL x. (EVEN x --> (EX m. x = 2 * m)) & (ODD x --> (EX m. x = Suc (2 * m)))"
  by (import arithmetic EVEN_ODD_EXISTS)

lemma EVEN_EXISTS: "ALL n. EVEN n = (EX m. n = 2 * m)"
  by (import arithmetic EVEN_EXISTS)

lemma ODD_EXISTS: "ALL n. ODD n = (EX m. n = Suc (2 * m))"
  by (import arithmetic ODD_EXISTS)

lemma NOT_SUC_LESS_EQ_0: "ALL x. ~ Suc x <= 0"
  by (import arithmetic NOT_SUC_LESS_EQ_0)

lemma NOT_LEQ: "ALL x xa. (~ x <= xa) = (Suc xa <= x)"
  by (import arithmetic NOT_LEQ)

lemma NOT_NUM_EQ: "ALL x xa. (x ~= xa) = (Suc x <= xa | Suc xa <= x)"
  by (import arithmetic NOT_NUM_EQ)

lemma NOT_GREATER_EQ: "ALL x xa. (~ xa <= x) = (Suc x <= xa)"
  by (import arithmetic NOT_GREATER_EQ)

lemma SUC_ADD_SYM: "ALL m n. Suc (m + n) = Suc n + m"
  by (import arithmetic SUC_ADD_SYM)

lemma NOT_SUC_ADD_LESS_EQ: "ALL m n. ~ Suc (m + n) <= m"
  by (import arithmetic NOT_SUC_ADD_LESS_EQ)

lemma SUB_LEFT_ADD: "ALL (m::nat) (n::nat) p::nat.
   m + (n - p) = (if n <= p then m else m + n - p)"
  by (import arithmetic SUB_LEFT_ADD)

lemma SUB_RIGHT_ADD: "ALL (m::nat) (n::nat) p::nat. m - n + p = (if m <= n then p else m + p - n)"
  by (import arithmetic SUB_RIGHT_ADD)

lemma SUB_LEFT_SUB: "ALL (m::nat) (n::nat) p::nat.
   m - (n - p) = (if n <= p then m else m + p - n)"
  by (import arithmetic SUB_LEFT_SUB)

lemma SUB_LEFT_SUC: "ALL m n. Suc (m - n) = (if m <= n then Suc 0 else Suc m - n)"
  by (import arithmetic SUB_LEFT_SUC)

lemma SUB_LEFT_LESS_EQ: "ALL (m::nat) (n::nat) p::nat. (m <= n - p) = (m + p <= n | m <= (0::nat))"
  by (import arithmetic SUB_LEFT_LESS_EQ)

lemma SUB_RIGHT_LESS_EQ: "ALL (m::nat) (n::nat) p::nat. (m - n <= p) = (m <= n + p)"
  by (import arithmetic SUB_RIGHT_LESS_EQ)

lemma SUB_RIGHT_LESS: "ALL (m::nat) (n::nat) p::nat. (m - n < p) = (m < n + p & (0::nat) < p)"
  by (import arithmetic SUB_RIGHT_LESS)

lemma SUB_RIGHT_GREATER_EQ: "ALL (m::nat) (n::nat) p::nat. (p <= m - n) = (n + p <= m | p <= (0::nat))"
  by (import arithmetic SUB_RIGHT_GREATER_EQ)

lemma SUB_LEFT_GREATER: "ALL (m::nat) (n::nat) p::nat. (n - p < m) = (n < m + p & (0::nat) < m)"
  by (import arithmetic SUB_LEFT_GREATER)

lemma SUB_RIGHT_GREATER: "ALL (m::nat) (n::nat) p::nat. (p < m - n) = (n + p < m)"
  by (import arithmetic SUB_RIGHT_GREATER)

lemma SUB_LEFT_EQ: "ALL (m::nat) (n::nat) p::nat.
   (m = n - p) = (m + p = n | m <= (0::nat) & n <= p)"
  by (import arithmetic SUB_LEFT_EQ)

lemma SUB_RIGHT_EQ: "ALL (m::nat) (n::nat) p::nat.
   (m - n = p) = (m = n + p | m <= n & p <= (0::nat))"
  by (import arithmetic SUB_RIGHT_EQ)

lemma LE: "(ALL n::nat. (n <= (0::nat)) = (n = (0::nat))) &
(ALL (m::nat) n::nat. (m <= Suc n) = (m = Suc n | m <= n))"
  by (import arithmetic LE)

lemma DA: "ALL (k::nat) n::nat.
   (0::nat) < n --> (EX (x::nat) q::nat. k = q * n + x & x < n)"
  by (import arithmetic DA)

lemma DIV_LESS_EQ: "ALL n::nat. (0::nat) < n --> (ALL k::nat. k div n <= k)"
  by (import arithmetic DIV_LESS_EQ)

lemma DIV_UNIQUE: "ALL (n::nat) (k::nat) q::nat.
   (EX r::nat. k = q * n + r & r < n) --> k div n = q"
  by (import arithmetic DIV_UNIQUE)

lemma MOD_UNIQUE: "ALL (n::nat) (k::nat) r::nat.
   (EX q::nat. k = q * n + r & r < n) --> k mod n = r"
  by (import arithmetic MOD_UNIQUE)

lemma DIV_MULT: "ALL (n::nat) r::nat. r < n --> (ALL q::nat. (q * n + r) div n = q)"
  by (import arithmetic DIV_MULT)

lemma MOD_EQ_0: "ALL n::nat. (0::nat) < n --> (ALL k::nat. k * n mod n = (0::nat))"
  by (import arithmetic MOD_EQ_0)

lemma ZERO_MOD: "ALL n::nat. (0::nat) < n --> (0::nat) mod n = (0::nat)"
  by (import arithmetic ZERO_MOD)

lemma ZERO_DIV: "ALL n::nat. (0::nat) < n --> (0::nat) div n = (0::nat)"
  by (import arithmetic ZERO_DIV)

lemma MOD_MULT: "ALL (n::nat) r::nat. r < n --> (ALL q::nat. (q * n + r) mod n = r)"
  by (import arithmetic MOD_MULT)

lemma MOD_TIMES: "ALL n::nat.
   (0::nat) < n --> (ALL (q::nat) r::nat. (q * n + r) mod n = r mod n)"
  by (import arithmetic MOD_TIMES)

lemma MOD_PLUS: "ALL n::nat.
   (0::nat) < n -->
   (ALL (j::nat) k::nat. (j mod n + k mod n) mod n = (j + k) mod n)"
  by (import arithmetic MOD_PLUS)

lemma MOD_MOD: "ALL n::nat. (0::nat) < n --> (ALL k::nat. k mod n mod n = k mod n)"
  by (import arithmetic MOD_MOD)

lemma ADD_DIV_ADD_DIV: "ALL x::nat.
   (0::nat) < x -->
   (ALL (xa::nat) r::nat. (xa * x + r) div x = xa + r div x)"
  by (import arithmetic ADD_DIV_ADD_DIV)

lemma MOD_MULT_MOD: "ALL (m::nat) n::nat.
   (0::nat) < n & (0::nat) < m -->
   (ALL x::nat. x mod (n * m) mod n = x mod n)"
  by (import arithmetic MOD_MULT_MOD)

lemma DIVMOD_ID: "ALL n::nat. (0::nat) < n --> n div n = (1::nat) & n mod n = (0::nat)"
  by (import arithmetic DIVMOD_ID)

lemma DIV_DIV_DIV_MULT: "ALL (x::nat) xa::nat.
   (0::nat) < x & (0::nat) < xa -->
   (ALL xb::nat. xb div x div xa = xb div (x * xa))"
  by (import arithmetic DIV_DIV_DIV_MULT)

lemma DIV_P: "ALL (P::nat => bool) (p::nat) q::nat.
   (0::nat) < q -->
   P (p div q) = (EX (k::nat) r::nat. p = k * q + r & r < q & P k)"
  by (import arithmetic DIV_P)

lemma MOD_P: "ALL (P::nat => bool) (p::nat) q::nat.
   (0::nat) < q -->
   P (p mod q) = (EX (k::nat) r::nat. p = k * q + r & r < q & P r)"
  by (import arithmetic MOD_P)

lemma MOD_TIMES2: "ALL n::nat.
   (0::nat) < n -->
   (ALL (j::nat) k::nat. j mod n * (k mod n) mod n = j * k mod n)"
  by (import arithmetic MOD_TIMES2)

lemma MOD_COMMON_FACTOR: "ALL (n::nat) (p::nat) q::nat.
   (0::nat) < n & (0::nat) < q --> n * (p mod q) = n * p mod (n * q)"
  by (import arithmetic MOD_COMMON_FACTOR)

lemma num_case_cong: "ALL M M' b f.
   M = M' & (M' = 0 --> b = b') & (ALL n. M' = Suc n --> f n = f' n) -->
   nat_case b f M = nat_case b' f' M'"
  by (import arithmetic num_case_cong)

lemma SUC_ELIM_THM: "ALL P. (ALL n. P (Suc n) n) = (ALL n. 0 < n --> P n (n - 1))"
  by (import arithmetic SUC_ELIM_THM)

lemma SUB_ELIM_THM: "(P::nat => bool) ((a::nat) - (b::nat)) =
(ALL x::nat. (b = a + x --> P (0::nat)) & (a = b + x --> P x))"
  by (import arithmetic SUB_ELIM_THM)

lemma PRE_ELIM_THM: "P (PRE n) = (ALL m. (n = 0 --> P 0) & (n = Suc m --> P m))"
  by (import arithmetic PRE_ELIM_THM)

lemma MULT_INCREASES: "ALL m n. 1 < m & 0 < n --> Suc n <= m * n"
  by (import arithmetic MULT_INCREASES)

lemma EXP_ALWAYS_BIG_ENOUGH: "ALL b::nat. (1::nat) < b --> (ALL n::nat. EX m::nat. n <= b ^ m)"
  by (import arithmetic EXP_ALWAYS_BIG_ENOUGH)

lemma EXP_EQ_0: "ALL (n::nat) m::nat. (n ^ m = (0::nat)) = (n = (0::nat) & (0::nat) < m)"
  by (import arithmetic EXP_EQ_0)

lemma EXP_1: "ALL x::nat. (1::nat) ^ x = (1::nat) & x ^ (1::nat) = x"
  by (import arithmetic EXP_1)

lemma EXP_EQ_1: "ALL (n::nat) m::nat. (n ^ m = (1::nat)) = (n = (1::nat) | m = (0::nat))"
  by (import arithmetic EXP_EQ_1)

lemma MIN_MAX_EQ: "ALL (x::nat) xa::nat. (min x xa = max x xa) = (x = xa)"
  by (import arithmetic MIN_MAX_EQ)

lemma MIN_MAX_LT: "ALL (x::nat) xa::nat. (min x xa < max x xa) = (x ~= xa)"
  by (import arithmetic MIN_MAX_LT)

lemma MIN_MAX_PRED: "ALL (P::nat => bool) (m::nat) n::nat.
   P m & P n --> P (min m n) & P (max m n)"
  by (import arithmetic MIN_MAX_PRED)

lemma MIN_LT: "ALL (x::nat) xa::nat.
   (min xa x < xa) = (xa ~= x & min xa x = x) &
   (min xa x < x) = (xa ~= x & min xa x = xa) &
   (xa < min xa x) = False & (x < min xa x) = False"
  by (import arithmetic MIN_LT)

lemma MAX_LT: "ALL (x::nat) xa::nat.
   (xa < max xa x) = (xa ~= x & max xa x = x) &
   (x < max xa x) = (xa ~= x & max xa x = xa) &
   (max xa x < xa) = False & (max xa x < x) = False"
  by (import arithmetic MAX_LT)

lemma MIN_LE: "ALL (x::nat) xa::nat. min xa x <= xa & min xa x <= x"
  by (import arithmetic MIN_LE)

lemma MAX_LE: "ALL (x::nat) xa::nat. xa <= max xa x & x <= max xa x"
  by (import arithmetic MAX_LE)

lemma MIN_0: "ALL x::nat. min x (0::nat) = (0::nat) & min (0::nat) x = (0::nat)"
  by (import arithmetic MIN_0)

lemma MAX_0: "ALL x::nat. max x (0::nat) = x & max (0::nat) x = x"
  by (import arithmetic MAX_0)

lemma EXISTS_GREATEST: "ALL P::nat => bool.
   (Ex P & (EX x::nat. ALL y::nat. x < y --> ~ P y)) =
   (EX x::nat. P x & (ALL y::nat. x < y --> ~ P y))"
  by (import arithmetic EXISTS_GREATEST)

;end_setup

;setup_theory hrat

constdefs
  trat_1 :: "nat * nat" 
  "trat_1 == (0, 0)"

lemma trat_1: "trat_1 = (0, 0)"
  by (import hrat trat_1)

constdefs
  trat_inv :: "nat * nat => nat * nat" 
  "trat_inv == %(x, y). (y, x)"

lemma trat_inv: "ALL x y. trat_inv (x, y) = (y, x)"
  by (import hrat trat_inv)

constdefs
  trat_add :: "nat * nat => nat * nat => nat * nat" 
  "trat_add ==
%(x, y) (x', y').
   (PRE (Suc x * Suc y' + Suc x' * Suc y), PRE (Suc y * Suc y'))"

lemma trat_add: "ALL x y x' y'.
   trat_add (x, y) (x', y') =
   (PRE (Suc x * Suc y' + Suc x' * Suc y), PRE (Suc y * Suc y'))"
  by (import hrat trat_add)

constdefs
  trat_mul :: "nat * nat => nat * nat => nat * nat" 
  "trat_mul == %(x, y) (x', y'). (PRE (Suc x * Suc x'), PRE (Suc y * Suc y'))"

lemma trat_mul: "ALL x y x' y'.
   trat_mul (x, y) (x', y') = (PRE (Suc x * Suc x'), PRE (Suc y * Suc y'))"
  by (import hrat trat_mul)

consts
  trat_sucint :: "nat => nat * nat" 

specification (trat_sucint) trat_sucint: "trat_sucint 0 = trat_1 &
(ALL n. trat_sucint (Suc n) = trat_add (trat_sucint n) trat_1)"
  by (import hrat trat_sucint)

constdefs
  trat_eq :: "nat * nat => nat * nat => bool" 
  "trat_eq == %(x, y) (x', y'). Suc x * Suc y' = Suc x' * Suc y"

lemma trat_eq: "ALL x y x' y'. trat_eq (x, y) (x', y') = (Suc x * Suc y' = Suc x' * Suc y)"
  by (import hrat trat_eq)

lemma TRAT_EQ_REFL: "ALL p. trat_eq p p"
  by (import hrat TRAT_EQ_REFL)

lemma TRAT_EQ_SYM: "ALL p q. trat_eq p q = trat_eq q p"
  by (import hrat TRAT_EQ_SYM)

lemma TRAT_EQ_TRANS: "ALL p q r. trat_eq p q & trat_eq q r --> trat_eq p r"
  by (import hrat TRAT_EQ_TRANS)

lemma TRAT_EQ_AP: "ALL p q. p = q --> trat_eq p q"
  by (import hrat TRAT_EQ_AP)

lemma TRAT_ADD_SYM_EQ: "ALL h i. trat_add h i = trat_add i h"
  by (import hrat TRAT_ADD_SYM_EQ)

lemma TRAT_MUL_SYM_EQ: "ALL h i. trat_mul h i = trat_mul i h"
  by (import hrat TRAT_MUL_SYM_EQ)

lemma TRAT_INV_WELLDEFINED: "ALL p q. trat_eq p q --> trat_eq (trat_inv p) (trat_inv q)"
  by (import hrat TRAT_INV_WELLDEFINED)

lemma TRAT_ADD_WELLDEFINED: "ALL p q r. trat_eq p q --> trat_eq (trat_add p r) (trat_add q r)"
  by (import hrat TRAT_ADD_WELLDEFINED)

lemma TRAT_ADD_WELLDEFINED2: "ALL p1 p2 q1 q2.
   trat_eq p1 p2 & trat_eq q1 q2 -->
   trat_eq (trat_add p1 q1) (trat_add p2 q2)"
  by (import hrat TRAT_ADD_WELLDEFINED2)

lemma TRAT_MUL_WELLDEFINED: "ALL p q r. trat_eq p q --> trat_eq (trat_mul p r) (trat_mul q r)"
  by (import hrat TRAT_MUL_WELLDEFINED)

lemma TRAT_MUL_WELLDEFINED2: "ALL p1 p2 q1 q2.
   trat_eq p1 p2 & trat_eq q1 q2 -->
   trat_eq (trat_mul p1 q1) (trat_mul p2 q2)"
  by (import hrat TRAT_MUL_WELLDEFINED2)

lemma TRAT_ADD_SYM: "ALL h i. trat_eq (trat_add h i) (trat_add i h)"
  by (import hrat TRAT_ADD_SYM)

lemma TRAT_ADD_ASSOC: "ALL h i j. trat_eq (trat_add h (trat_add i j)) (trat_add (trat_add h i) j)"
  by (import hrat TRAT_ADD_ASSOC)

lemma TRAT_MUL_SYM: "ALL h i. trat_eq (trat_mul h i) (trat_mul i h)"
  by (import hrat TRAT_MUL_SYM)

lemma TRAT_MUL_ASSOC: "ALL h i j. trat_eq (trat_mul h (trat_mul i j)) (trat_mul (trat_mul h i) j)"
  by (import hrat TRAT_MUL_ASSOC)

lemma TRAT_LDISTRIB: "ALL h i j.
   trat_eq (trat_mul h (trat_add i j))
    (trat_add (trat_mul h i) (trat_mul h j))"
  by (import hrat TRAT_LDISTRIB)

lemma TRAT_MUL_LID: "ALL h. trat_eq (trat_mul trat_1 h) h"
  by (import hrat TRAT_MUL_LID)

lemma TRAT_MUL_LINV: "ALL h. trat_eq (trat_mul (trat_inv h) h) trat_1"
  by (import hrat TRAT_MUL_LINV)

lemma TRAT_NOZERO: "ALL h i. ~ trat_eq (trat_add h i) h"
  by (import hrat TRAT_NOZERO)

lemma TRAT_ADD_TOTAL: "ALL h i.
   trat_eq h i |
   (EX d. trat_eq h (trat_add i d)) | (EX d. trat_eq i (trat_add h d))"
  by (import hrat TRAT_ADD_TOTAL)

lemma TRAT_SUCINT_0: "ALL n. trat_eq (trat_sucint n) (n, 0)"
  by (import hrat TRAT_SUCINT_0)

lemma TRAT_ARCH: "ALL h. EX n d. trat_eq (trat_sucint n) (trat_add h d)"
  by (import hrat TRAT_ARCH)

lemma TRAT_SUCINT: "trat_eq (trat_sucint 0) trat_1 &
(ALL n. trat_eq (trat_sucint (Suc n)) (trat_add (trat_sucint n) trat_1))"
  by (import hrat TRAT_SUCINT)

lemma TRAT_EQ_EQUIV: "ALL p q. trat_eq p q = (trat_eq p = trat_eq q)"
  by (import hrat TRAT_EQ_EQUIV)

typedef (open) hrat = "{x. EX xa. x = trat_eq xa}" 
  by (rule typedef_helper,import hrat hrat_TY_DEF)

lemmas hrat_TY_DEF = typedef_hol2hol4 [OF type_definition_hrat]

consts
  mk_hrat :: "(nat * nat => bool) => hrat" 
  dest_hrat :: "hrat => nat * nat => bool" 

specification (dest_hrat mk_hrat) hrat_tybij: "(ALL a. mk_hrat (dest_hrat a) = a) &
(ALL r. (EX x. r = trat_eq x) = (dest_hrat (mk_hrat r) = r))"
  by (import hrat hrat_tybij)

constdefs
  hrat_1 :: "hrat" 
  "hrat_1 == mk_hrat (trat_eq trat_1)"

lemma hrat_1: "hrat_1 = mk_hrat (trat_eq trat_1)"
  by (import hrat hrat_1)

constdefs
  hrat_inv :: "hrat => hrat" 
  "hrat_inv == %T1. mk_hrat (trat_eq (trat_inv (Eps (dest_hrat T1))))"

lemma hrat_inv: "ALL T1. hrat_inv T1 = mk_hrat (trat_eq (trat_inv (Eps (dest_hrat T1))))"
  by (import hrat hrat_inv)

constdefs
  hrat_add :: "hrat => hrat => hrat" 
  "hrat_add ==
%T1 T2.
   mk_hrat (trat_eq (trat_add (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"

lemma hrat_add: "ALL T1 T2.
   hrat_add T1 T2 =
   mk_hrat (trat_eq (trat_add (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"
  by (import hrat hrat_add)

constdefs
  hrat_mul :: "hrat => hrat => hrat" 
  "hrat_mul ==
%T1 T2.
   mk_hrat (trat_eq (trat_mul (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"

lemma hrat_mul: "ALL T1 T2.
   hrat_mul T1 T2 =
   mk_hrat (trat_eq (trat_mul (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"
  by (import hrat hrat_mul)

constdefs
  hrat_sucint :: "nat => hrat" 
  "hrat_sucint == %T1. mk_hrat (trat_eq (trat_sucint T1))"

lemma hrat_sucint: "ALL T1. hrat_sucint T1 = mk_hrat (trat_eq (trat_sucint T1))"
  by (import hrat hrat_sucint)

lemma HRAT_ADD_SYM: "ALL h i. hrat_add h i = hrat_add i h"
  by (import hrat HRAT_ADD_SYM)

lemma HRAT_ADD_ASSOC: "ALL h i j. hrat_add h (hrat_add i j) = hrat_add (hrat_add h i) j"
  by (import hrat HRAT_ADD_ASSOC)

lemma HRAT_MUL_SYM: "ALL h i. hrat_mul h i = hrat_mul i h"
  by (import hrat HRAT_MUL_SYM)

lemma HRAT_MUL_ASSOC: "ALL h i j. hrat_mul h (hrat_mul i j) = hrat_mul (hrat_mul h i) j"
  by (import hrat HRAT_MUL_ASSOC)

lemma HRAT_LDISTRIB: "ALL h i j.
   hrat_mul h (hrat_add i j) = hrat_add (hrat_mul h i) (hrat_mul h j)"
  by (import hrat HRAT_LDISTRIB)

lemma HRAT_MUL_LID: "ALL h. hrat_mul hrat_1 h = h"
  by (import hrat HRAT_MUL_LID)

lemma HRAT_MUL_LINV: "ALL h. hrat_mul (hrat_inv h) h = hrat_1"
  by (import hrat HRAT_MUL_LINV)

lemma HRAT_NOZERO: "ALL h i. hrat_add h i ~= h"
  by (import hrat HRAT_NOZERO)

lemma HRAT_ADD_TOTAL: "ALL h i. h = i | (EX x. h = hrat_add i x) | (EX x. i = hrat_add h x)"
  by (import hrat HRAT_ADD_TOTAL)

lemma HRAT_ARCH: "ALL h. EX x xa. hrat_sucint x = hrat_add h xa"
  by (import hrat HRAT_ARCH)

lemma HRAT_SUCINT: "hrat_sucint 0 = hrat_1 &
(ALL x. hrat_sucint (Suc x) = hrat_add (hrat_sucint x) hrat_1)"
  by (import hrat HRAT_SUCINT)

;end_setup

;setup_theory hreal

constdefs
  hrat_lt :: "hrat => hrat => bool" 
  "hrat_lt == %x y. EX d. y = hrat_add x d"

lemma hrat_lt: "ALL x y. hrat_lt x y = (EX d. y = hrat_add x d)"
  by (import hreal hrat_lt)

lemma HRAT_LT_REFL: "ALL x. ~ hrat_lt x x"
  by (import hreal HRAT_LT_REFL)

lemma HRAT_LT_TRANS: "ALL x y z. hrat_lt x y & hrat_lt y z --> hrat_lt x z"
  by (import hreal HRAT_LT_TRANS)

lemma HRAT_LT_ANTISYM: "ALL x y. ~ (hrat_lt x y & hrat_lt y x)"
  by (import hreal HRAT_LT_ANTISYM)

lemma HRAT_LT_TOTAL: "ALL x y. x = y | hrat_lt x y | hrat_lt y x"
  by (import hreal HRAT_LT_TOTAL)

lemma HRAT_MUL_RID: "ALL x. hrat_mul x hrat_1 = x"
  by (import hreal HRAT_MUL_RID)

lemma HRAT_MUL_RINV: "ALL x. hrat_mul x (hrat_inv x) = hrat_1"
  by (import hreal HRAT_MUL_RINV)

lemma HRAT_RDISTRIB: "ALL x y z.
   hrat_mul (hrat_add x y) z = hrat_add (hrat_mul x z) (hrat_mul y z)"
  by (import hreal HRAT_RDISTRIB)

lemma HRAT_LT_ADDL: "ALL x y. hrat_lt x (hrat_add x y)"
  by (import hreal HRAT_LT_ADDL)

lemma HRAT_LT_ADDR: "ALL x xa. hrat_lt xa (hrat_add x xa)"
  by (import hreal HRAT_LT_ADDR)

lemma HRAT_LT_GT: "ALL x y. hrat_lt x y --> ~ hrat_lt y x"
  by (import hreal HRAT_LT_GT)

lemma HRAT_LT_NE: "ALL x y. hrat_lt x y --> x ~= y"
  by (import hreal HRAT_LT_NE)

lemma HRAT_EQ_LADD: "ALL x y z. (hrat_add x y = hrat_add x z) = (y = z)"
  by (import hreal HRAT_EQ_LADD)

lemma HRAT_EQ_LMUL: "ALL x y z. (hrat_mul x y = hrat_mul x z) = (y = z)"
  by (import hreal HRAT_EQ_LMUL)

lemma HRAT_LT_ADD2: "ALL u v x y.
   hrat_lt u x & hrat_lt v y --> hrat_lt (hrat_add u v) (hrat_add x y)"
  by (import hreal HRAT_LT_ADD2)

lemma HRAT_LT_LADD: "ALL x y z. hrat_lt (hrat_add z x) (hrat_add z y) = hrat_lt x y"
  by (import hreal HRAT_LT_LADD)

lemma HRAT_LT_RADD: "ALL x y z. hrat_lt (hrat_add x z) (hrat_add y z) = hrat_lt x y"
  by (import hreal HRAT_LT_RADD)

lemma HRAT_LT_MUL2: "ALL u v x y.
   hrat_lt u x & hrat_lt v y --> hrat_lt (hrat_mul u v) (hrat_mul x y)"
  by (import hreal HRAT_LT_MUL2)

lemma HRAT_LT_LMUL: "ALL x y z. hrat_lt (hrat_mul z x) (hrat_mul z y) = hrat_lt x y"
  by (import hreal HRAT_LT_LMUL)

lemma HRAT_LT_RMUL: "ALL x y z. hrat_lt (hrat_mul x z) (hrat_mul y z) = hrat_lt x y"
  by (import hreal HRAT_LT_RMUL)

lemma HRAT_LT_LMUL1: "ALL x y. hrat_lt (hrat_mul x y) y = hrat_lt x hrat_1"
  by (import hreal HRAT_LT_LMUL1)

lemma HRAT_LT_RMUL1: "ALL x y. hrat_lt (hrat_mul x y) x = hrat_lt y hrat_1"
  by (import hreal HRAT_LT_RMUL1)

lemma HRAT_GT_LMUL1: "ALL x y. hrat_lt y (hrat_mul x y) = hrat_lt hrat_1 x"
  by (import hreal HRAT_GT_LMUL1)

lemma HRAT_LT_L1: "ALL x y. hrat_lt (hrat_mul (hrat_inv x) y) hrat_1 = hrat_lt y x"
  by (import hreal HRAT_LT_L1)

lemma HRAT_LT_R1: "ALL x y. hrat_lt (hrat_mul x (hrat_inv y)) hrat_1 = hrat_lt x y"
  by (import hreal HRAT_LT_R1)

lemma HRAT_GT_L1: "ALL x y. hrat_lt hrat_1 (hrat_mul (hrat_inv x) y) = hrat_lt x y"
  by (import hreal HRAT_GT_L1)

lemma HRAT_INV_MUL: "ALL x y. hrat_inv (hrat_mul x y) = hrat_mul (hrat_inv x) (hrat_inv y)"
  by (import hreal HRAT_INV_MUL)

lemma HRAT_UP: "ALL x. Ex (hrat_lt x)"
  by (import hreal HRAT_UP)

lemma HRAT_DOWN: "ALL x. EX xa. hrat_lt xa x"
  by (import hreal HRAT_DOWN)

lemma HRAT_DOWN2: "ALL x y. EX xa. hrat_lt xa x & hrat_lt xa y"
  by (import hreal HRAT_DOWN2)

lemma HRAT_MEAN: "ALL x y. hrat_lt x y --> (EX xa. hrat_lt x xa & hrat_lt xa y)"
  by (import hreal HRAT_MEAN)

constdefs
  isacut :: "(hrat => bool) => bool" 
  "isacut ==
%C. Ex C &
    (EX x. ~ C x) &
    (ALL x y. C x & hrat_lt y x --> C y) &
    (ALL x. C x --> (EX y. C y & hrat_lt x y))"

lemma isacut: "ALL C.
   isacut C =
   (Ex C &
    (EX x. ~ C x) &
    (ALL x y. C x & hrat_lt y x --> C y) &
    (ALL x. C x --> (EX y. C y & hrat_lt x y)))"
  by (import hreal isacut)

constdefs
  cut_of_hrat :: "hrat => hrat => bool" 
  "cut_of_hrat == %x y. hrat_lt y x"

lemma cut_of_hrat: "ALL x. cut_of_hrat x = (%y. hrat_lt y x)"
  by (import hreal cut_of_hrat)

lemma ISACUT_HRAT: "ALL h. isacut (cut_of_hrat h)"
  by (import hreal ISACUT_HRAT)

typedef (open) hreal = "Collect isacut" 
  by (rule typedef_helper,import hreal hreal_TY_DEF)

lemmas hreal_TY_DEF = typedef_hol2hol4 [OF type_definition_hreal]

consts
  hreal :: "(hrat => bool) => hreal" 
  cut :: "hreal => hrat => bool" 

specification (cut hreal) hreal_tybij: "(ALL a. hreal (hreal.cut a) = a) &
(ALL r. isacut r = (hreal.cut (hreal r) = r))"
  by (import hreal hreal_tybij)

lemma EQUAL_CUTS: "ALL X Y. hreal.cut X = hreal.cut Y --> X = Y"
  by (import hreal EQUAL_CUTS)

lemma CUT_ISACUT: "ALL x. isacut (hreal.cut x)"
  by (import hreal CUT_ISACUT)

lemma CUT_NONEMPTY: "ALL x. Ex (hreal.cut x)"
  by (import hreal CUT_NONEMPTY)

lemma CUT_BOUNDED: "ALL x. EX xa. ~ hreal.cut x xa"
  by (import hreal CUT_BOUNDED)

lemma CUT_DOWN: "ALL x xa xb. hreal.cut x xa & hrat_lt xb xa --> hreal.cut x xb"
  by (import hreal CUT_DOWN)

lemma CUT_UP: "ALL x xa. hreal.cut x xa --> (EX y. hreal.cut x y & hrat_lt xa y)"
  by (import hreal CUT_UP)

lemma CUT_UBOUND: "ALL x xa xb. ~ hreal.cut x xa & hrat_lt xa xb --> ~ hreal.cut x xb"
  by (import hreal CUT_UBOUND)

lemma CUT_STRADDLE: "ALL X x y. hreal.cut X x & ~ hreal.cut X y --> hrat_lt x y"
  by (import hreal CUT_STRADDLE)

lemma CUT_NEARTOP_ADD: "ALL X e. EX x. hreal.cut X x & ~ hreal.cut X (hrat_add x e)"
  by (import hreal CUT_NEARTOP_ADD)

lemma CUT_NEARTOP_MUL: "ALL X u.
   hrat_lt hrat_1 u --> (EX x. hreal.cut X x & ~ hreal.cut X (hrat_mul u x))"
  by (import hreal CUT_NEARTOP_MUL)

constdefs
  hreal_1 :: "hreal" 
  "hreal_1 == hreal (cut_of_hrat hrat_1)"

lemma hreal_1: "hreal_1 = hreal (cut_of_hrat hrat_1)"
  by (import hreal hreal_1)

constdefs
  hreal_add :: "hreal => hreal => hreal" 
  "hreal_add ==
%X Y. hreal (%w. EX x y. w = hrat_add x y & hreal.cut X x & hreal.cut Y y)"

lemma hreal_add: "ALL X Y.
   hreal_add X Y =
   hreal (%w. EX x y. w = hrat_add x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal hreal_add)

constdefs
  hreal_mul :: "hreal => hreal => hreal" 
  "hreal_mul ==
%X Y. hreal (%w. EX x y. w = hrat_mul x y & hreal.cut X x & hreal.cut Y y)"

lemma hreal_mul: "ALL X Y.
   hreal_mul X Y =
   hreal (%w. EX x y. w = hrat_mul x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal hreal_mul)

constdefs
  hreal_inv :: "hreal => hreal" 
  "hreal_inv ==
%X. hreal
     (%w. EX d. hrat_lt d hrat_1 &
                (ALL x. hreal.cut X x --> hrat_lt (hrat_mul w x) d))"

lemma hreal_inv: "ALL X.
   hreal_inv X =
   hreal
    (%w. EX d. hrat_lt d hrat_1 &
               (ALL x. hreal.cut X x --> hrat_lt (hrat_mul w x) d))"
  by (import hreal hreal_inv)

constdefs
  hreal_sup :: "(hreal => bool) => hreal" 
  "hreal_sup == %P. hreal (%w. EX X. P X & hreal.cut X w)"

lemma hreal_sup: "ALL P. hreal_sup P = hreal (%w. EX X. P X & hreal.cut X w)"
  by (import hreal hreal_sup)

constdefs
  hreal_lt :: "hreal => hreal => bool" 
  "hreal_lt == %X Y. X ~= Y & (ALL x. hreal.cut X x --> hreal.cut Y x)"

lemma hreal_lt: "ALL X Y. hreal_lt X Y = (X ~= Y & (ALL x. hreal.cut X x --> hreal.cut Y x))"
  by (import hreal hreal_lt)

lemma HREAL_INV_ISACUT: "ALL X.
   isacut
    (%w. EX d. hrat_lt d hrat_1 &
               (ALL x. hreal.cut X x --> hrat_lt (hrat_mul w x) d))"
  by (import hreal HREAL_INV_ISACUT)

lemma HREAL_ADD_ISACUT: "ALL X Y.
   isacut (%w. EX x y. w = hrat_add x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal HREAL_ADD_ISACUT)

lemma HREAL_MUL_ISACUT: "ALL X Y.
   isacut (%w. EX x y. w = hrat_mul x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal HREAL_MUL_ISACUT)

lemma HREAL_ADD_SYM: "ALL X Y. hreal_add X Y = hreal_add Y X"
  by (import hreal HREAL_ADD_SYM)

lemma HREAL_MUL_SYM: "ALL X Y. hreal_mul X Y = hreal_mul Y X"
  by (import hreal HREAL_MUL_SYM)

lemma HREAL_ADD_ASSOC: "ALL X Y Z. hreal_add X (hreal_add Y Z) = hreal_add (hreal_add X Y) Z"
  by (import hreal HREAL_ADD_ASSOC)

lemma HREAL_MUL_ASSOC: "ALL X Y Z. hreal_mul X (hreal_mul Y Z) = hreal_mul (hreal_mul X Y) Z"
  by (import hreal HREAL_MUL_ASSOC)

lemma HREAL_LDISTRIB: "ALL X Y Z.
   hreal_mul X (hreal_add Y Z) = hreal_add (hreal_mul X Y) (hreal_mul X Z)"
  by (import hreal HREAL_LDISTRIB)

lemma HREAL_MUL_LID: "ALL X. hreal_mul hreal_1 X = X"
  by (import hreal HREAL_MUL_LID)

lemma HREAL_MUL_LINV: "ALL X. hreal_mul (hreal_inv X) X = hreal_1"
  by (import hreal HREAL_MUL_LINV)

lemma HREAL_NOZERO: "ALL X Y. hreal_add X Y ~= X"
  by (import hreal HREAL_NOZERO)

constdefs
  hreal_sub :: "hreal => hreal => hreal" 
  "hreal_sub ==
%Y X. hreal (%w. EX x. ~ hreal.cut X x & hreal.cut Y (hrat_add x w))"

lemma hreal_sub: "ALL Y X.
   hreal_sub Y X =
   hreal (%w. EX x. ~ hreal.cut X x & hreal.cut Y (hrat_add x w))"
  by (import hreal hreal_sub)

lemma HREAL_LT_LEMMA: "ALL X Y. hreal_lt X Y --> (EX x. ~ hreal.cut X x & hreal.cut Y x)"
  by (import hreal HREAL_LT_LEMMA)

lemma HREAL_SUB_ISACUT: "ALL X Y.
   hreal_lt X Y -->
   isacut (%w. EX x. ~ hreal.cut X x & hreal.cut Y (hrat_add x w))"
  by (import hreal HREAL_SUB_ISACUT)

lemma HREAL_SUB_ADD: "ALL X Y. hreal_lt X Y --> hreal_add (hreal_sub Y X) X = Y"
  by (import hreal HREAL_SUB_ADD)

lemma HREAL_LT_TOTAL: "ALL X Y. X = Y | hreal_lt X Y | hreal_lt Y X"
  by (import hreal HREAL_LT_TOTAL)

lemma HREAL_LT: "ALL X Y. hreal_lt X Y = (EX D. Y = hreal_add X D)"
  by (import hreal HREAL_LT)

lemma HREAL_ADD_TOTAL: "ALL X Y. X = Y | (EX D. Y = hreal_add X D) | (EX D. X = hreal_add Y D)"
  by (import hreal HREAL_ADD_TOTAL)

lemma HREAL_SUP_ISACUT: "ALL P.
   Ex P & (EX Y. ALL X. P X --> hreal_lt X Y) -->
   isacut (%w. EX X. P X & hreal.cut X w)"
  by (import hreal HREAL_SUP_ISACUT)

lemma HREAL_SUP: "ALL P.
   Ex P & (EX Y. ALL X. P X --> hreal_lt X Y) -->
   (ALL Y. (EX X. P X & hreal_lt Y X) = hreal_lt Y (hreal_sup P))"
  by (import hreal HREAL_SUP)

;end_setup

;setup_theory numeral

lemma numeral_suc: "Suc ALT_ZERO = NUMERAL_BIT1 ALT_ZERO &
(ALL x. Suc (NUMERAL_BIT1 x) = NUMERAL_BIT2 x) &
(ALL x. Suc (NUMERAL_BIT2 x) = NUMERAL_BIT1 (Suc x))"
  by (import numeral numeral_suc)

constdefs
  iZ :: "nat => nat" 
  "iZ == %x. x"

lemma iZ: "ALL x. iZ x = x"
  by (import numeral iZ)

constdefs
  iiSUC :: "nat => nat" 
  "iiSUC == %n. Suc (Suc n)"

lemma iiSUC: "ALL n. iiSUC n = Suc (Suc n)"
  by (import numeral iiSUC)

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
  by (import numeral numeral_distrib)

lemma numeral_iisuc: "iiSUC ALT_ZERO = NUMERAL_BIT2 ALT_ZERO &
iiSUC (NUMERAL_BIT1 n) = NUMERAL_BIT1 (Suc n) &
iiSUC (NUMERAL_BIT2 n) = NUMERAL_BIT2 (Suc n)"
  by (import numeral numeral_iisuc)

lemma numeral_add: "ALL x xa.
   iZ (ALT_ZERO + x) = x &
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
   iiSUC (NUMERAL_BIT1 x + NUMERAL_BIT2 xa) =
   NUMERAL_BIT1 (iiSUC (x + xa)) &
   iiSUC (NUMERAL_BIT2 x + NUMERAL_BIT1 xa) =
   NUMERAL_BIT1 (iiSUC (x + xa)) &
   iiSUC (NUMERAL_BIT2 x + NUMERAL_BIT2 xa) = NUMERAL_BIT2 (iiSUC (x + xa))"
  by (import numeral numeral_add)

lemma numeral_eq: "ALL x xa.
   (ALT_ZERO = NUMERAL_BIT1 x) = False &
   (NUMERAL_BIT1 x = ALT_ZERO) = False &
   (ALT_ZERO = NUMERAL_BIT2 x) = False &
   (NUMERAL_BIT2 x = ALT_ZERO) = False &
   (NUMERAL_BIT1 x = NUMERAL_BIT2 xa) = False &
   (NUMERAL_BIT2 x = NUMERAL_BIT1 xa) = False &
   (NUMERAL_BIT1 x = NUMERAL_BIT1 xa) = (x = xa) &
   (NUMERAL_BIT2 x = NUMERAL_BIT2 xa) = (x = xa)"
  by (import numeral numeral_eq)

lemma numeral_lt: "ALL x xa.
   (ALT_ZERO < NUMERAL_BIT1 x) = True &
   (ALT_ZERO < NUMERAL_BIT2 x) = True &
   (x < ALT_ZERO) = False &
   (NUMERAL_BIT1 x < NUMERAL_BIT1 xa) = (x < xa) &
   (NUMERAL_BIT2 x < NUMERAL_BIT2 xa) = (x < xa) &
   (NUMERAL_BIT1 x < NUMERAL_BIT2 xa) = (~ xa < x) &
   (NUMERAL_BIT2 x < NUMERAL_BIT1 xa) = (x < xa)"
  by (import numeral numeral_lt)

lemma numeral_lte: "ALL x xa.
   (ALT_ZERO <= x) = True &
   (NUMERAL_BIT1 x <= ALT_ZERO) = False &
   (NUMERAL_BIT2 x <= ALT_ZERO) = False &
   (NUMERAL_BIT1 x <= NUMERAL_BIT1 xa) = (x <= xa) &
   (NUMERAL_BIT1 x <= NUMERAL_BIT2 xa) = (x <= xa) &
   (NUMERAL_BIT2 x <= NUMERAL_BIT1 xa) = (~ xa <= x) &
   (NUMERAL_BIT2 x <= NUMERAL_BIT2 xa) = (x <= xa)"
  by (import numeral numeral_lte)

lemma numeral_pre: "PRE ALT_ZERO = ALT_ZERO &
PRE (NUMERAL_BIT1 ALT_ZERO) = ALT_ZERO &
(ALL x.
    PRE (NUMERAL_BIT1 (NUMERAL_BIT1 x)) =
    NUMERAL_BIT2 (PRE (NUMERAL_BIT1 x))) &
(ALL x.
    PRE (NUMERAL_BIT1 (NUMERAL_BIT2 x)) = NUMERAL_BIT2 (NUMERAL_BIT1 x)) &
(ALL x. PRE (NUMERAL_BIT2 x) = NUMERAL_BIT1 x)"
  by (import numeral numeral_pre)

lemma bit_initiality: "ALL zf b1f b2f.
   EX x. x ALT_ZERO = zf &
         (ALL n. x (NUMERAL_BIT1 n) = b1f n (x n)) &
         (ALL n. x (NUMERAL_BIT2 n) = b2f n (x n))"
  by (import numeral bit_initiality)

consts
  iBIT_cases :: "nat => 'a => (nat => 'a) => (nat => 'a) => 'a" 

specification (iBIT_cases) iBIT_cases: "(ALL (zf::'a) (bf1::nat => 'a) bf2::nat => 'a.
    iBIT_cases ALT_ZERO zf bf1 bf2 = zf) &
(ALL (n::nat) (zf::'a) (bf1::nat => 'a) bf2::nat => 'a.
    iBIT_cases (NUMERAL_BIT1 n) zf bf1 bf2 = bf1 n) &
(ALL (n::nat) (zf::'a) (bf1::nat => 'a) bf2::nat => 'a.
    iBIT_cases (NUMERAL_BIT2 n) zf bf1 bf2 = bf2 n)"
  by (import numeral iBIT_cases)

constdefs
  iDUB :: "nat => nat" 
  "iDUB == %x. x + x"

lemma iDUB: "ALL x. iDUB x = x + x"
  by (import numeral iDUB)

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
  by (import numeral iSUB_DEF)

lemma bit_induction: "ALL P.
   P ALT_ZERO &
   (ALL n. P n --> P (NUMERAL_BIT1 n)) &
   (ALL n. P n --> P (NUMERAL_BIT2 n)) -->
   All P"
  by (import numeral bit_induction)

lemma iSUB_THM: "ALL xa xb xc.
   iSUB xa ALT_ZERO x = ALT_ZERO &
   iSUB True xb ALT_ZERO = xb &
   iSUB False (NUMERAL_BIT1 xb) ALT_ZERO = iDUB xb &
   iSUB True (NUMERAL_BIT1 xb) (NUMERAL_BIT1 xc) = iDUB (iSUB True xb xc) &
   iSUB False (NUMERAL_BIT1 xb) (NUMERAL_BIT1 xc) =
   NUMERAL_BIT1 (iSUB False xb xc) &
   iSUB True (NUMERAL_BIT1 xb) (NUMERAL_BIT2 xc) =
   NUMERAL_BIT1 (iSUB False xb xc) &
   iSUB False (NUMERAL_BIT1 xb) (NUMERAL_BIT2 xc) =
   iDUB (iSUB False xb xc) &
   iSUB False (NUMERAL_BIT2 xb) ALT_ZERO = NUMERAL_BIT1 xb &
   iSUB True (NUMERAL_BIT2 xb) (NUMERAL_BIT1 xc) =
   NUMERAL_BIT1 (iSUB True xb xc) &
   iSUB False (NUMERAL_BIT2 xb) (NUMERAL_BIT1 xc) = iDUB (iSUB True xb xc) &
   iSUB True (NUMERAL_BIT2 xb) (NUMERAL_BIT2 xc) = iDUB (iSUB True xb xc) &
   iSUB False (NUMERAL_BIT2 xb) (NUMERAL_BIT2 xc) =
   NUMERAL_BIT1 (iSUB False xb xc)"
  by (import numeral iSUB_THM)

lemma numeral_sub: "ALL x xa.
   NUMERAL (x - xa) = (if xa < x then NUMERAL (iSUB True x xa) else 0)"
  by (import numeral numeral_sub)

lemma iDUB_removal: "ALL x.
   iDUB (NUMERAL_BIT1 x) = NUMERAL_BIT2 (iDUB x) &
   iDUB (NUMERAL_BIT2 x) = NUMERAL_BIT2 (NUMERAL_BIT1 x) &
   iDUB ALT_ZERO = ALT_ZERO"
  by (import numeral iDUB_removal)

lemma numeral_mult: "ALL x xa.
   ALT_ZERO * x = ALT_ZERO &
   x * ALT_ZERO = ALT_ZERO &
   NUMERAL_BIT1 x * xa = iZ (iDUB (x * xa) + xa) &
   NUMERAL_BIT2 x * xa = iDUB (iZ (x * xa + xa))"
  by (import numeral numeral_mult)

constdefs
  iSQR :: "nat => nat" 
  "iSQR == %x. x * x"

lemma iSQR: "ALL x. iSQR x = x * x"
  by (import numeral iSQR)

lemma numeral_exp: "(ALL x. x ^ ALT_ZERO = NUMERAL_BIT1 ALT_ZERO) &
(ALL x xa. x ^ NUMERAL_BIT1 xa = x * iSQR (x ^ xa)) &
(ALL x xa. x ^ NUMERAL_BIT2 xa = iSQR x * iSQR (x ^ xa))"
  by (import numeral numeral_exp)

lemma numeral_evenodd: "ALL x.
   EVEN ALT_ZERO &
   EVEN (NUMERAL_BIT2 x) &
   ~ EVEN (NUMERAL_BIT1 x) &
   ~ ODD ALT_ZERO & ~ ODD (NUMERAL_BIT2 x) & ODD (NUMERAL_BIT1 x)"
  by (import numeral numeral_evenodd)

lemma numeral_fact: "ALL n. FACT n = (if n = 0 then 1 else n * FACT (PRE n))"
  by (import numeral numeral_fact)

lemma numeral_funpow: "ALL n. (f ^ n) x = (if n = 0 then x else (f ^ (n - 1)) (f x))"
  by (import numeral numeral_funpow)

;end_setup

;setup_theory ind_type

lemma INJ_INVERSE2: "ALL P::'A => 'B => 'C.
   (ALL (x1::'A) (y1::'B) (x2::'A) y2::'B.
       (P x1 y1 = P x2 y2) = (x1 = x2 & y1 = y2)) -->
   (EX (x::'C => 'A) Y::'C => 'B.
       ALL (xa::'A) y::'B. x (P xa y) = xa & Y (P xa y) = y)"
  by (import ind_type INJ_INVERSE2)

constdefs
  NUMPAIR :: "nat => nat => nat" 
  "NUMPAIR == %x y. 2 ^ x * (2 * y + 1)"

lemma NUMPAIR: "ALL x y. NUMPAIR x y = 2 ^ x * (2 * y + 1)"
  by (import ind_type NUMPAIR)

lemma NUMPAIR_INJ_LEMMA: "ALL x xa xb xc. NUMPAIR x xa = NUMPAIR xb xc --> x = xb"
  by (import ind_type NUMPAIR_INJ_LEMMA)

lemma NUMPAIR_INJ: "ALL x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2 & y1 = y2)"
  by (import ind_type NUMPAIR_INJ)

consts
  NUMSND :: "nat => nat" 
  NUMFST :: "nat => nat" 

specification (NUMFST NUMSND) NUMPAIR_DEST: "ALL x y. NUMFST (NUMPAIR x y) = x & NUMSND (NUMPAIR x y) = y"
  by (import ind_type NUMPAIR_DEST)

constdefs
  NUMSUM :: "bool => nat => nat" 
  "NUMSUM == %b x. if b then Suc (2 * x) else 2 * x"

lemma NUMSUM: "ALL b x. NUMSUM b x = (if b then Suc (2 * x) else 2 * x)"
  by (import ind_type NUMSUM)

lemma NUMSUM_INJ: "ALL b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2 & x1 = x2)"
  by (import ind_type NUMSUM_INJ)

consts
  NUMRIGHT :: "nat => nat" 
  NUMLEFT :: "nat => bool" 

specification (NUMLEFT NUMRIGHT) NUMSUM_DEST: "ALL x y. NUMLEFT (NUMSUM x y) = x & NUMRIGHT (NUMSUM x y) = y"
  by (import ind_type NUMSUM_DEST)

constdefs
  INJN :: "nat => nat => 'a => bool" 
  "INJN == %m n a. n = m"

lemma INJN: "ALL m. INJN m = (%n a. n = m)"
  by (import ind_type INJN)

lemma INJN_INJ: "ALL n1 n2. (INJN n1 = INJN n2) = (n1 = n2)"
  by (import ind_type INJN_INJ)

constdefs
  INJA :: "'a => nat => 'a => bool" 
  "INJA == %a n b. b = a"

lemma INJA: "ALL a. INJA a = (%n b. b = a)"
  by (import ind_type INJA)

lemma INJA_INJ: "ALL a1 a2. (INJA a1 = INJA a2) = (a1 = a2)"
  by (import ind_type INJA_INJ)

constdefs
  INJF :: "(nat => nat => 'a => bool) => nat => 'a => bool" 
  "INJF == %f n. f (NUMFST n) (NUMSND n)"

lemma INJF: "ALL f. INJF f = (%n. f (NUMFST n) (NUMSND n))"
  by (import ind_type INJF)

lemma INJF_INJ: "ALL f1 f2. (INJF f1 = INJF f2) = (f1 = f2)"
  by (import ind_type INJF_INJ)

constdefs
  INJP :: "(nat => 'a => bool) => (nat => 'a => bool) => nat => 'a => bool" 
  "INJP ==
%f1 f2 n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a"

lemma INJP: "ALL f1 f2.
   INJP f1 f2 =
   (%n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a)"
  by (import ind_type INJP)

lemma INJP_INJ: "ALL f1 f1' f2 f2'. (INJP f1 f2 = INJP f1' f2') = (f1 = f1' & f2 = f2')"
  by (import ind_type INJP_INJ)

constdefs
  ZCONSTR :: "nat => 'a => (nat => nat => 'a => bool) => nat => 'a => bool" 
  "ZCONSTR == %c i r. INJP (INJN (Suc c)) (INJP (INJA i) (INJF r))"

lemma ZCONSTR: "ALL c i r. ZCONSTR c i r = INJP (INJN (Suc c)) (INJP (INJA i) (INJF r))"
  by (import ind_type ZCONSTR)

constdefs
  ZBOT :: "nat => 'a => bool" 
  "ZBOT == INJP (INJN 0) (SOME z. True)"

lemma ZBOT: "ZBOT = INJP (INJN 0) (SOME z. True)"
  by (import ind_type ZBOT)

lemma ZCONSTR_ZBOT: "ALL x xa xb. ZCONSTR x xa xb ~= ZBOT"
  by (import ind_type ZCONSTR_ZBOT)

constdefs
  ZRECSPACE :: "(nat => 'a => bool) => bool" 
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
  by (import ind_type ZRECSPACE)

lemma ZRECSPACE_rules: "(op &::bool => bool => bool)
 ((ZRECSPACE::(nat => 'a => bool) => bool) (ZBOT::nat => 'a => bool))
 ((All::(nat => bool) => bool)
   (%c::nat.
       (All::('a => bool) => bool)
        (%i::'a.
            (All::((nat => nat => 'a => bool) => bool) => bool)
             (%r::nat => nat => 'a => bool.
                 (op -->::bool => bool => bool)
                  ((All::(nat => bool) => bool)
                    (%n::nat.
                        (ZRECSPACE::(nat => 'a => bool) => bool) (r n)))
                  ((ZRECSPACE::(nat => 'a => bool) => bool)
                    ((ZCONSTR::nat
                               => 'a => (nat => nat => 'a => bool)
  => nat => 'a => bool)
                      c i r))))))"
  by (import ind_type ZRECSPACE_rules)

lemma ZRECSPACE_ind: "ALL x.
   x ZBOT & (ALL c i r. (ALL n. x (r n)) --> x (ZCONSTR c i r)) -->
   (ALL a0. ZRECSPACE a0 --> x a0)"
  by (import ind_type ZRECSPACE_ind)

lemma ZRECSPACE_cases: "ALL a0.
   ZRECSPACE a0 =
   (a0 = ZBOT | (EX c i r. a0 = ZCONSTR c i r & (ALL n. ZRECSPACE (r n))))"
  by (import ind_type ZRECSPACE_cases)

typedef (open) ('a) recspace = "(Collect::((nat => 'a => bool) => bool) => (nat => 'a => bool) set)
 (ZRECSPACE::(nat => 'a => bool) => bool)" 
  by (rule typedef_helper,import ind_type recspace_TY_DEF)

lemmas recspace_TY_DEF = typedef_hol2hol4 [OF type_definition_recspace]

consts
  mk_rec :: "(nat => 'a => bool) => 'a recspace" 
  dest_rec :: "'a recspace => nat => 'a => bool" 

specification (dest_rec mk_rec) recspace_repfns: "(ALL a::'a recspace. mk_rec (dest_rec a) = a) &
(ALL r::nat => 'a => bool. ZRECSPACE r = (dest_rec (mk_rec r) = r))"
  by (import ind_type recspace_repfns)

constdefs
  BOTTOM :: "'a recspace" 
  "BOTTOM == mk_rec ZBOT"

lemma BOTTOM: "BOTTOM = mk_rec ZBOT"
  by (import ind_type BOTTOM)

constdefs
  CONSTR :: "nat => 'a => (nat => 'a recspace) => 'a recspace" 
  "CONSTR == %c i r. mk_rec (ZCONSTR c i (%n. dest_rec (r n)))"

lemma CONSTR: "ALL c i r. CONSTR c i r = mk_rec (ZCONSTR c i (%n. dest_rec (r n)))"
  by (import ind_type CONSTR)

lemma MK_REC_INJ: "ALL x y. mk_rec x = mk_rec y --> ZRECSPACE x & ZRECSPACE y --> x = y"
  by (import ind_type MK_REC_INJ)

lemma DEST_REC_INJ: "ALL x y. (dest_rec x = dest_rec y) = (x = y)"
  by (import ind_type DEST_REC_INJ)

lemma CONSTR_BOT: "ALL c i r. CONSTR c i r ~= BOTTOM"
  by (import ind_type CONSTR_BOT)

lemma CONSTR_INJ: "ALL c1 i1 r1 c2 i2 r2.
   (CONSTR c1 i1 r1 = CONSTR c2 i2 r2) = (c1 = c2 & i1 = i2 & r1 = r2)"
  by (import ind_type CONSTR_INJ)

lemma CONSTR_IND: "ALL P.
   P BOTTOM & (ALL c i r. (ALL n. P (r n)) --> P (CONSTR c i r)) --> All P"
  by (import ind_type CONSTR_IND)

lemma CONSTR_REC: "ALL Fn. EX f. ALL c i r. f (CONSTR c i r) = Fn c i r (%n. f (r n))"
  by (import ind_type CONSTR_REC)

consts
  FCONS :: "'a => (nat => 'a) => nat => 'a" 

specification (FCONS) FCONS: "(ALL (a::'a) f::nat => 'a. FCONS a f (0::nat) = a) &
(ALL (a::'a) (f::nat => 'a) n::nat. FCONS a f (Suc n) = f n)"
  by (import ind_type FCONS)

constdefs
  FNIL :: "nat => 'a" 
  "FNIL == %n. SOME x. True"

lemma FNIL: "ALL n. FNIL n = (SOME x. True)"
  by (import ind_type FNIL)

constdefs
  ISO :: "('a => 'b) => ('b => 'a) => bool" 
  "ISO == %f g. (ALL x. f (g x) = x) & (ALL y. g (f y) = y)"

lemma ISO: "ALL f g. ISO f g = ((ALL x. f (g x) = x) & (ALL y. g (f y) = y))"
  by (import ind_type ISO)

lemma ISO_REFL: "ISO (%x. x) (%x. x)"
  by (import ind_type ISO_REFL)

lemma ISO_FUN: "ISO (f::'a => 'c) (f'::'c => 'a) & ISO (g::'b => 'd) (g'::'d => 'b) -->
ISO (%(h::'a => 'b) a'::'c. g (h (f' a')))
 (%(h::'c => 'd) a::'a. g' (h (f a)))"
  by (import ind_type ISO_FUN)

lemma ISO_USAGE: "ISO f g -->
(ALL P. All P = (ALL x. P (g x))) &
(ALL P. Ex P = (EX x. P (g x))) & (ALL a b. (a = g b) = (f a = b))"
  by (import ind_type ISO_USAGE)

;end_setup

;setup_theory divides

lemma ONE_DIVIDES_ALL: "All (op dvd (1::nat))"
  by (import divides ONE_DIVIDES_ALL)

lemma DIVIDES_ADD_2: "ALL (a::nat) (b::nat) c::nat. a dvd b & a dvd b + c --> a dvd c"
  by (import divides DIVIDES_ADD_2)

lemma NOT_LT_DIV: "ALL (a::nat) b::nat. (0::nat) < b & b < a --> ~ a dvd b"
  by (import divides NOT_LT_DIV)

lemma DIVIDES_FACT: "ALL b. 0 < b --> b dvd FACT b"
  by (import divides DIVIDES_FACT)

lemma DIVIDES_MULT_LEFT: "ALL (x::nat) xa::nat. (x * xa dvd xa) = (xa = (0::nat) | x = (1::nat))"
  by (import divides DIVIDES_MULT_LEFT)

;end_setup

;setup_theory prime

consts
  prime :: "nat => bool" 

defs
  prime_primdef: "prime.prime == %a. a ~= 1 & (ALL b. b dvd a --> b = a | b = 1)"

lemma prime_def: "ALL a. prime.prime a = (a ~= 1 & (ALL b. b dvd a --> b = a | b = 1))"
  by (import prime prime_def)

lemma NOT_PRIME_0: "~ prime.prime 0"
  by (import prime NOT_PRIME_0)

lemma NOT_PRIME_1: "~ prime.prime 1"
  by (import prime NOT_PRIME_1)

;end_setup

;setup_theory list

consts
  EL :: "nat => 'a list => 'a" 

specification (EL) EL: "(ALL l::'a list. EL (0::nat) l = hd l) &
(ALL (l::'a list) n::nat. EL (Suc n) l = EL n (tl l))"
  by (import list EL)

lemma NULL: "(op &::bool => bool => bool) ((null::'a list => bool) ([]::'a list))
 ((All::('a => bool) => bool)
   (%x::'a.
       (All::('a list => bool) => bool)
        (%xa::'a list.
            (Not::bool => bool)
             ((null::'a list => bool)
               ((op #::'a => 'a list => 'a list) x xa)))))"
  by (import list NULL)

lemma list_case_compute: "ALL l. list_case b f l = (if null l then b else f (hd l) (tl l))"
  by (import list list_case_compute)

lemma LIST_NOT_EQ: "ALL l1 l2. l1 ~= l2 --> (ALL x xa. x # l1 ~= xa # l2)"
  by (import list LIST_NOT_EQ)

lemma NOT_EQ_LIST: "ALL h1 h2. h1 ~= h2 --> (ALL x xa. h1 # x ~= h2 # xa)"
  by (import list NOT_EQ_LIST)

lemma EQ_LIST: "ALL h1 h2. h1 = h2 --> (ALL l1 l2. l1 = l2 --> h1 # l1 = h2 # l2)"
  by (import list EQ_LIST)

lemma CONS: "ALL l. ~ null l --> hd l # tl l = l"
  by (import list CONS)

lemma MAP_EQ_NIL: "ALL l f. (map f l = []) = (l = []) & ([] = map f l) = (l = [])"
  by (import list MAP_EQ_NIL)

lemma EVERY_EL: "(All::('a list => bool) => bool)
 (%l::'a list.
     (All::(('a => bool) => bool) => bool)
      (%P::'a => bool.
          (op =::bool => bool => bool)
           ((list_all::('a => bool) => 'a list => bool) P l)
           ((All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <::nat => nat => bool) n ((size::'a list => nat) l))
                  (P ((EL::nat => 'a list => 'a) n l))))))"
  by (import list EVERY_EL)

lemma EVERY_CONJ: "ALL l. list_all (%x. P x & Q x) l = (list_all P l & list_all Q l)"
  by (import list EVERY_CONJ)

lemma EVERY_MEM: "ALL P l. list_all P l = (ALL e. e mem l --> P e)"
  by (import list EVERY_MEM)

lemma EXISTS_MEM: "ALL P l. list_exists P l = (EX e. e mem l & P e)"
  by (import list EXISTS_MEM)

lemma MEM_APPEND: "ALL e l1 l2. e mem l1 @ l2 = (e mem l1 | e mem l2)"
  by (import list MEM_APPEND)

lemma EXISTS_APPEND: "ALL P l1 l2. list_exists P (l1 @ l2) = (list_exists P l1 | list_exists P l2)"
  by (import list EXISTS_APPEND)

lemma NOT_EVERY: "ALL P l. (~ list_all P l) = list_exists (Not o P) l"
  by (import list NOT_EVERY)

lemma NOT_EXISTS: "ALL P l. (~ list_exists P l) = list_all (Not o P) l"
  by (import list NOT_EXISTS)

lemma MEM_MAP: "ALL l f x. x mem map f l = (EX y. x = f y & y mem l)"
  by (import list MEM_MAP)

lemma LENGTH_CONS: "ALL l n. (length l = Suc n) = (EX h l'. length l' = n & l = h # l')"
  by (import list LENGTH_CONS)

lemma LENGTH_EQ_CONS: "ALL P n.
   (ALL l. length l = Suc n --> P l) =
   (ALL l. length l = n --> (ALL x. P (x # l)))"
  by (import list LENGTH_EQ_CONS)

lemma LENGTH_EQ_NIL: "ALL P. (ALL l. length l = 0 --> P l) = P []"
  by (import list LENGTH_EQ_NIL)

lemma CONS_ACYCLIC: "ALL l x. l ~= x # l & x # l ~= l"
  by (import list CONS_ACYCLIC)

lemma APPEND_eq_NIL: "(ALL (l1::'a list) l2::'a list. ([] = l1 @ l2) = (l1 = [] & l2 = [])) &
(ALL (l1::'a list) l2::'a list. (l1 @ l2 = []) = (l1 = [] & l2 = []))"
  by (import list APPEND_eq_NIL)

lemma APPEND_11: "(ALL (l1::'a list) (l2::'a list) l3::'a list.
    (l1 @ l2 = l1 @ l3) = (l2 = l3)) &
(ALL (l1::'a list) (l2::'a list) l3::'a list.
    (l2 @ l1 = l3 @ l1) = (l2 = l3))"
  by (import list APPEND_11)

lemma EL_compute: "ALL n. EL n l = (if n = 0 then hd l else EL (PRE n) (tl l))"
  by (import list EL_compute)

lemma WF_LIST_PRED: "WF (%L1 L2. EX h. L2 = h # L1)"
  by (import list WF_LIST_PRED)

lemma list_size_cong: "ALL M N f f'.
   M = N & (ALL x. x mem N --> f x = f' x) -->
   list_size f M = list_size f' N"
  by (import list list_size_cong)

lemma FOLDR_CONG: "ALL l l' b b' f f'.
   l = l' & b = b' & (ALL x a. x mem l' --> f x a = f' x a) -->
   foldr f l b = foldr f' l' b'"
  by (import list FOLDR_CONG)

lemma FOLDL_CONG: "ALL l l' b b' f f'.
   l = l' & b = b' & (ALL x a. x mem l' --> f a x = f' a x) -->
   foldl f b l = foldl f' b' l'"
  by (import list FOLDL_CONG)

lemma MAP_CONG: "ALL l1 l2 f f'.
   l1 = l2 & (ALL x. x mem l2 --> f x = f' x) --> map f l1 = map f' l2"
  by (import list MAP_CONG)

lemma EXISTS_CONG: "ALL l1 l2 P P'.
   l1 = l2 & (ALL x. x mem l2 --> P x = P' x) -->
   list_exists P l1 = list_exists P' l2"
  by (import list EXISTS_CONG)

lemma EVERY_CONG: "ALL l1 l2 P P'.
   l1 = l2 & (ALL x. x mem l2 --> P x = P' x) -->
   list_all P l1 = list_all P' l2"
  by (import list EVERY_CONG)

lemma EVERY_MONOTONIC: "ALL P Q. (ALL x. P x --> Q x) --> (ALL l. list_all P l --> list_all Q l)"
  by (import list EVERY_MONOTONIC)

lemma LENGTH_ZIP: "ALL l1 l2.
   length l1 = length l2 -->
   length (zip l1 l2) = length l1 & length (zip l1 l2) = length l2"
  by (import list LENGTH_ZIP)

lemma LENGTH_UNZIP: "ALL pl.
   length (fst (unzip pl)) = length pl & length (snd (unzip pl)) = length pl"
  by (import list LENGTH_UNZIP)

lemma ZIP_UNZIP: "ALL l. ZIP (unzip l) = l"
  by (import list ZIP_UNZIP)

lemma UNZIP_ZIP: "ALL l1 l2. length l1 = length l2 --> unzip (zip l1 l2) = (l1, l2)"
  by (import list UNZIP_ZIP)

lemma ZIP_MAP: "ALL l1 l2 f1 f2.
   length l1 = length l2 -->
   zip (map f1 l1) l2 = map (%p. (f1 (fst p), snd p)) (zip l1 l2) &
   zip l1 (map f2 l2) = map (%p. (fst p, f2 (snd p))) (zip l1 l2)"
  by (import list ZIP_MAP)

lemma MEM_ZIP: "(All::('a list => bool) => bool)
 (%l1::'a list.
     (All::('b list => bool) => bool)
      (%l2::'b list.
          (All::('a * 'b => bool) => bool)
           (%p::'a * 'b.
               (op -->::bool => bool => bool)
                ((op =::nat => nat => bool) ((size::'a list => nat) l1)
                  ((size::'b list => nat) l2))
                ((op =::bool => bool => bool)
                  ((op mem::'a * 'b => ('a * 'b) list => bool) p
                    ((zip::'a list => 'b list => ('a * 'b) list) l1 l2))
                  ((Ex::(nat => bool) => bool)
                    (%n::nat.
                        (op &::bool => bool => bool)
                         ((op <::nat => nat => bool) n
                           ((size::'a list => nat) l1))
                         ((op =::'a * 'b => 'a * 'b => bool) p
                           ((Pair::'a => 'b => 'a * 'b)
                             ((EL::nat => 'a list => 'a) n l1)
                             ((EL::nat => 'b list => 'b) n l2)))))))))"
  by (import list MEM_ZIP)

lemma EL_ZIP: "ALL l1 l2 n.
   length l1 = length l2 & n < length l1 -->
   EL n (zip l1 l2) = (EL n l1, EL n l2)"
  by (import list EL_ZIP)

lemma MAP2_ZIP: "ALL l1 l2.
   length l1 = length l2 -->
   (ALL f. map2 f l1 l2 = map (split f) (zip l1 l2))"
  by (import list MAP2_ZIP)

lemma MEM_EL: "(All::('a list => bool) => bool)
 (%l::'a list.
     (All::('a => bool) => bool)
      (%x::'a.
          (op =::bool => bool => bool) ((op mem::'a => 'a list => bool) x l)
           ((Ex::(nat => bool) => bool)
             (%n::nat.
                 (op &::bool => bool => bool)
                  ((op <::nat => nat => bool) n ((size::'a list => nat) l))
                  ((op =::'a => 'a => bool) x
                    ((EL::nat => 'a list => 'a) n l))))))"
  by (import list MEM_EL)

lemma LAST_CONS: "(ALL x::'a. last [x] = x) &
(ALL (x::'a) (xa::'a) xb::'a list. last (x # xa # xb) = last (xa # xb))"
  by (import list LAST_CONS)

lemma FRONT_CONS: "(ALL x::'a. butlast [x] = []) &
(ALL (x::'a) (xa::'a) xb::'a list.
    butlast (x # xa # xb) = x # butlast (xa # xb))"
  by (import list FRONT_CONS)

;end_setup

;setup_theory pred_set

lemma EXTENSION: "ALL s t. (s = t) = (ALL x. IN x s = IN x t)"
  by (import pred_set EXTENSION)

lemma NOT_EQUAL_SETS: "ALL x xa. (x ~= xa) = (EX xb. IN xb xa = (~ IN xb x))"
  by (import pred_set NOT_EQUAL_SETS)

lemma NUM_SET_WOP: "ALL s::nat => bool.
   (EX n::nat. IN n s) =
   (EX n::nat. IN n s & (ALL m::nat. IN m s --> n <= m))"
  by (import pred_set NUM_SET_WOP)

consts
  GSPEC :: "('b => 'a * bool) => 'a => bool" 

specification (GSPEC) GSPECIFICATION: "ALL (f::'b => 'a * bool) v::'a. IN v (GSPEC f) = (EX x::'b. (v, True) = f x)"
  by (import pred_set GSPECIFICATION)

lemma SET_MINIMUM: "ALL (s::'a => bool) M::'a => nat.
   (EX x::'a. IN x s) =
   (EX x::'a. IN x s & (ALL y::'a. IN y s --> M x <= M y))"
  by (import pred_set SET_MINIMUM)

constdefs
  EMPTY :: "'a => bool" 
  "EMPTY == %x. False"

lemma EMPTY_DEF: "EMPTY = (%x. False)"
  by (import pred_set EMPTY_DEF)

lemma NOT_IN_EMPTY: "ALL x. ~ IN x EMPTY"
  by (import pred_set NOT_IN_EMPTY)

lemma MEMBER_NOT_EMPTY: "ALL x. (EX xa. IN xa x) = (x ~= EMPTY)"
  by (import pred_set MEMBER_NOT_EMPTY)

consts
  UNIV :: "'a => bool" 

defs
  UNIV_def: "pred_set.UNIV == %x. True"

lemma UNIV_DEF: "pred_set.UNIV = (%x. True)"
  by (import pred_set UNIV_DEF)

lemma IN_UNIV: "ALL x. IN x pred_set.UNIV"
  by (import pred_set IN_UNIV)

lemma UNIV_NOT_EMPTY: "pred_set.UNIV ~= EMPTY"
  by (import pred_set UNIV_NOT_EMPTY)

lemma EMPTY_NOT_UNIV: "EMPTY ~= pred_set.UNIV"
  by (import pred_set EMPTY_NOT_UNIV)

lemma EQ_UNIV: "(ALL x. IN x s) = (s = pred_set.UNIV)"
  by (import pred_set EQ_UNIV)

constdefs
  SUBSET :: "('a => bool) => ('a => bool) => bool" 
  "SUBSET == %s t. ALL x. IN x s --> IN x t"

lemma SUBSET_DEF: "ALL s t. SUBSET s t = (ALL x. IN x s --> IN x t)"
  by (import pred_set SUBSET_DEF)

lemma SUBSET_TRANS: "ALL x xa xb. SUBSET x xa & SUBSET xa xb --> SUBSET x xb"
  by (import pred_set SUBSET_TRANS)

lemma SUBSET_REFL: "ALL x. SUBSET x x"
  by (import pred_set SUBSET_REFL)

lemma SUBSET_ANTISYM: "ALL x xa. SUBSET x xa & SUBSET xa x --> x = xa"
  by (import pred_set SUBSET_ANTISYM)

lemma EMPTY_SUBSET: "All (SUBSET EMPTY)"
  by (import pred_set EMPTY_SUBSET)

lemma SUBSET_EMPTY: "ALL x. SUBSET x EMPTY = (x = EMPTY)"
  by (import pred_set SUBSET_EMPTY)

lemma SUBSET_UNIV: "ALL x. SUBSET x pred_set.UNIV"
  by (import pred_set SUBSET_UNIV)

lemma UNIV_SUBSET: "ALL x. SUBSET pred_set.UNIV x = (x = pred_set.UNIV)"
  by (import pred_set UNIV_SUBSET)

constdefs
  PSUBSET :: "('a => bool) => ('a => bool) => bool" 
  "PSUBSET == %s t. SUBSET s t & s ~= t"

lemma PSUBSET_DEF: "ALL s t. PSUBSET s t = (SUBSET s t & s ~= t)"
  by (import pred_set PSUBSET_DEF)

lemma PSUBSET_TRANS: "ALL x xa xb. PSUBSET x xa & PSUBSET xa xb --> PSUBSET x xb"
  by (import pred_set PSUBSET_TRANS)

lemma PSUBSET_IRREFL: "ALL x. ~ PSUBSET x x"
  by (import pred_set PSUBSET_IRREFL)

lemma NOT_PSUBSET_EMPTY: "ALL x. ~ PSUBSET x EMPTY"
  by (import pred_set NOT_PSUBSET_EMPTY)

lemma NOT_UNIV_PSUBSET: "ALL x. ~ PSUBSET pred_set.UNIV x"
  by (import pred_set NOT_UNIV_PSUBSET)

lemma PSUBSET_UNIV: "ALL x. PSUBSET x pred_set.UNIV = (EX xa. ~ IN xa x)"
  by (import pred_set PSUBSET_UNIV)

consts
  UNION :: "('a => bool) => ('a => bool) => 'a => bool" 

defs
  UNION_def: "pred_set.UNION == %s t. GSPEC (%x. (x, IN x s | IN x t))"

lemma UNION_DEF: "ALL s t. pred_set.UNION s t = GSPEC (%x. (x, IN x s | IN x t))"
  by (import pred_set UNION_DEF)

lemma IN_UNION: "ALL x xa xb. IN xb (pred_set.UNION x xa) = (IN xb x | IN xb xa)"
  by (import pred_set IN_UNION)

lemma UNION_ASSOC: "ALL x xa xb.
   pred_set.UNION x (pred_set.UNION xa xb) =
   pred_set.UNION (pred_set.UNION x xa) xb"
  by (import pred_set UNION_ASSOC)

lemma UNION_IDEMPOT: "ALL x. pred_set.UNION x x = x"
  by (import pred_set UNION_IDEMPOT)

lemma UNION_COMM: "ALL x xa. pred_set.UNION x xa = pred_set.UNION xa x"
  by (import pred_set UNION_COMM)

lemma SUBSET_UNION: "(ALL (x::'a => bool) xa::'a => bool. SUBSET x (pred_set.UNION x xa)) &
(ALL (x::'a => bool) xa::'a => bool. SUBSET x (pred_set.UNION xa x))"
  by (import pred_set SUBSET_UNION)

lemma UNION_SUBSET: "ALL s t u. SUBSET (pred_set.UNION s t) u = (SUBSET s u & SUBSET t u)"
  by (import pred_set UNION_SUBSET)

lemma SUBSET_UNION_ABSORPTION: "ALL x xa. SUBSET x xa = (pred_set.UNION x xa = xa)"
  by (import pred_set SUBSET_UNION_ABSORPTION)

lemma UNION_EMPTY: "(ALL x::'a => bool. pred_set.UNION EMPTY x = x) &
(ALL x::'a => bool. pred_set.UNION x EMPTY = x)"
  by (import pred_set UNION_EMPTY)

lemma UNION_UNIV: "(ALL x::'a => bool. pred_set.UNION pred_set.UNIV x = pred_set.UNIV) &
(ALL x::'a => bool. pred_set.UNION x pred_set.UNIV = pred_set.UNIV)"
  by (import pred_set UNION_UNIV)

lemma EMPTY_UNION: "ALL x xa. (pred_set.UNION x xa = EMPTY) = (x = EMPTY & xa = EMPTY)"
  by (import pred_set EMPTY_UNION)

consts
  INTER :: "('a => bool) => ('a => bool) => 'a => bool" 

defs
  INTER_def: "pred_set.INTER == %s t. GSPEC (%x. (x, IN x s & IN x t))"

lemma INTER_DEF: "ALL s t. pred_set.INTER s t = GSPEC (%x. (x, IN x s & IN x t))"
  by (import pred_set INTER_DEF)

lemma IN_INTER: "ALL x xa xb. IN xb (pred_set.INTER x xa) = (IN xb x & IN xb xa)"
  by (import pred_set IN_INTER)

lemma INTER_ASSOC: "ALL x xa xb.
   pred_set.INTER x (pred_set.INTER xa xb) =
   pred_set.INTER (pred_set.INTER x xa) xb"
  by (import pred_set INTER_ASSOC)

lemma INTER_IDEMPOT: "ALL x. pred_set.INTER x x = x"
  by (import pred_set INTER_IDEMPOT)

lemma INTER_COMM: "ALL x xa. pred_set.INTER x xa = pred_set.INTER xa x"
  by (import pred_set INTER_COMM)

lemma INTER_SUBSET: "(ALL (x::'a => bool) xa::'a => bool. SUBSET (pred_set.INTER x xa) x) &
(ALL (x::'a => bool) xa::'a => bool. SUBSET (pred_set.INTER xa x) x)"
  by (import pred_set INTER_SUBSET)

lemma SUBSET_INTER: "ALL s t u. SUBSET s (pred_set.INTER t u) = (SUBSET s t & SUBSET s u)"
  by (import pred_set SUBSET_INTER)

lemma SUBSET_INTER_ABSORPTION: "ALL x xa. SUBSET x xa = (pred_set.INTER x xa = x)"
  by (import pred_set SUBSET_INTER_ABSORPTION)

lemma INTER_EMPTY: "(ALL x::'a => bool. pred_set.INTER EMPTY x = EMPTY) &
(ALL x::'a => bool. pred_set.INTER x EMPTY = EMPTY)"
  by (import pred_set INTER_EMPTY)

lemma INTER_UNIV: "(ALL x::'a => bool. pred_set.INTER pred_set.UNIV x = x) &
(ALL x::'a => bool. pred_set.INTER x pred_set.UNIV = x)"
  by (import pred_set INTER_UNIV)

lemma UNION_OVER_INTER: "ALL x xa xb.
   pred_set.INTER x (pred_set.UNION xa xb) =
   pred_set.UNION (pred_set.INTER x xa) (pred_set.INTER x xb)"
  by (import pred_set UNION_OVER_INTER)

lemma INTER_OVER_UNION: "ALL x xa xb.
   pred_set.UNION x (pred_set.INTER xa xb) =
   pred_set.INTER (pred_set.UNION x xa) (pred_set.UNION x xb)"
  by (import pred_set INTER_OVER_UNION)

constdefs
  DISJOINT :: "('a => bool) => ('a => bool) => bool" 
  "DISJOINT == %s t. pred_set.INTER s t = EMPTY"

lemma DISJOINT_DEF: "ALL s t. DISJOINT s t = (pred_set.INTER s t = EMPTY)"
  by (import pred_set DISJOINT_DEF)

lemma IN_DISJOINT: "ALL x xa. DISJOINT x xa = (~ (EX xb. IN xb x & IN xb xa))"
  by (import pred_set IN_DISJOINT)

lemma DISJOINT_SYM: "ALL x xa. DISJOINT x xa = DISJOINT xa x"
  by (import pred_set DISJOINT_SYM)

lemma DISJOINT_EMPTY: "ALL x. DISJOINT EMPTY x & DISJOINT x EMPTY"
  by (import pred_set DISJOINT_EMPTY)

lemma DISJOINT_EMPTY_REFL: "ALL x. (x = EMPTY) = DISJOINT x x"
  by (import pred_set DISJOINT_EMPTY_REFL)

lemma DISJOINT_UNION: "ALL x xa xb.
   DISJOINT (pred_set.UNION x xa) xb = (DISJOINT x xb & DISJOINT xa xb)"
  by (import pred_set DISJOINT_UNION)

lemma DISJOINT_UNION_BOTH: "ALL s t u.
   DISJOINT (pred_set.UNION s t) u = (DISJOINT s u & DISJOINT t u) &
   DISJOINT u (pred_set.UNION s t) = (DISJOINT s u & DISJOINT t u)"
  by (import pred_set DISJOINT_UNION_BOTH)

constdefs
  DIFF :: "('a => bool) => ('a => bool) => 'a => bool" 
  "DIFF == %s t. GSPEC (%x. (x, IN x s & ~ IN x t))"

lemma DIFF_DEF: "ALL s t. DIFF s t = GSPEC (%x. (x, IN x s & ~ IN x t))"
  by (import pred_set DIFF_DEF)

lemma IN_DIFF: "ALL s t x. IN x (DIFF s t) = (IN x s & ~ IN x t)"
  by (import pred_set IN_DIFF)

lemma DIFF_EMPTY: "ALL s. DIFF s EMPTY = s"
  by (import pred_set DIFF_EMPTY)

lemma EMPTY_DIFF: "ALL s. DIFF EMPTY s = EMPTY"
  by (import pred_set EMPTY_DIFF)

lemma DIFF_UNIV: "ALL s. DIFF s pred_set.UNIV = EMPTY"
  by (import pred_set DIFF_UNIV)

lemma DIFF_DIFF: "ALL x xa. DIFF (DIFF x xa) xa = DIFF x xa"
  by (import pred_set DIFF_DIFF)

lemma DIFF_EQ_EMPTY: "ALL x. DIFF x x = EMPTY"
  by (import pred_set DIFF_EQ_EMPTY)

constdefs
  INSERT :: "'a => ('a => bool) => 'a => bool" 
  "INSERT == %x s. GSPEC (%y. (y, y = x | IN y s))"

lemma INSERT_DEF: "ALL x s. INSERT x s = GSPEC (%y. (y, y = x | IN y s))"
  by (import pred_set INSERT_DEF)

lemma IN_INSERT: "ALL x xa xb. IN x (INSERT xa xb) = (x = xa | IN x xb)"
  by (import pred_set IN_INSERT)

lemma COMPONENT: "ALL x xa. IN x (INSERT x xa)"
  by (import pred_set COMPONENT)

lemma SET_CASES: "ALL x. x = EMPTY | (EX xa xb. x = INSERT xa xb & ~ IN xa xb)"
  by (import pred_set SET_CASES)

lemma DECOMPOSITION: "ALL s x. IN x s = (EX t. s = INSERT x t & ~ IN x t)"
  by (import pred_set DECOMPOSITION)

lemma ABSORPTION: "ALL x xa. IN x xa = (INSERT x xa = xa)"
  by (import pred_set ABSORPTION)

lemma INSERT_INSERT: "ALL x xa. INSERT x (INSERT x xa) = INSERT x xa"
  by (import pred_set INSERT_INSERT)

lemma INSERT_COMM: "ALL x xa xb. INSERT x (INSERT xa xb) = INSERT xa (INSERT x xb)"
  by (import pred_set INSERT_COMM)

lemma INSERT_UNIV: "ALL x. INSERT x pred_set.UNIV = pred_set.UNIV"
  by (import pred_set INSERT_UNIV)

lemma NOT_INSERT_EMPTY: "ALL x xa. INSERT x xa ~= EMPTY"
  by (import pred_set NOT_INSERT_EMPTY)

lemma NOT_EMPTY_INSERT: "ALL x xa. EMPTY ~= INSERT x xa"
  by (import pred_set NOT_EMPTY_INSERT)

lemma INSERT_UNION: "ALL x s t.
   pred_set.UNION (INSERT x s) t =
   (if IN x t then pred_set.UNION s t else INSERT x (pred_set.UNION s t))"
  by (import pred_set INSERT_UNION)

lemma INSERT_UNION_EQ: "ALL x s t. pred_set.UNION (INSERT x s) t = INSERT x (pred_set.UNION s t)"
  by (import pred_set INSERT_UNION_EQ)

lemma INSERT_INTER: "ALL x s t.
   pred_set.INTER (INSERT x s) t =
   (if IN x t then INSERT x (pred_set.INTER s t) else pred_set.INTER s t)"
  by (import pred_set INSERT_INTER)

lemma DISJOINT_INSERT: "ALL x xa xb. DISJOINT (INSERT x xa) xb = (DISJOINT xa xb & ~ IN x xb)"
  by (import pred_set DISJOINT_INSERT)

lemma INSERT_SUBSET: "ALL x xa xb. SUBSET (INSERT x xa) xb = (IN x xb & SUBSET xa xb)"
  by (import pred_set INSERT_SUBSET)

lemma SUBSET_INSERT: "ALL x xa. ~ IN x xa --> (ALL xb. SUBSET xa (INSERT x xb) = SUBSET xa xb)"
  by (import pred_set SUBSET_INSERT)

lemma INSERT_DIFF: "ALL s t x.
   DIFF (INSERT x s) t = (if IN x t then DIFF s t else INSERT x (DIFF s t))"
  by (import pred_set INSERT_DIFF)

constdefs
  DELETE :: "('a => bool) => 'a => 'a => bool" 
  "DELETE == %s x. DIFF s (INSERT x EMPTY)"

lemma DELETE_DEF: "ALL s x. DELETE s x = DIFF s (INSERT x EMPTY)"
  by (import pred_set DELETE_DEF)

lemma IN_DELETE: "ALL x xa xb. IN xa (DELETE x xb) = (IN xa x & xa ~= xb)"
  by (import pred_set IN_DELETE)

lemma DELETE_NON_ELEMENT: "ALL x xa. (~ IN x xa) = (DELETE xa x = xa)"
  by (import pred_set DELETE_NON_ELEMENT)

lemma IN_DELETE_EQ: "ALL s x x'. (IN x s = IN x' s) = (IN x (DELETE s x') = IN x' (DELETE s x))"
  by (import pred_set IN_DELETE_EQ)

lemma EMPTY_DELETE: "ALL x. DELETE EMPTY x = EMPTY"
  by (import pred_set EMPTY_DELETE)

lemma DELETE_DELETE: "ALL x xa. DELETE (DELETE xa x) x = DELETE xa x"
  by (import pred_set DELETE_DELETE)

lemma DELETE_COMM: "ALL x xa xb. DELETE (DELETE xb x) xa = DELETE (DELETE xb xa) x"
  by (import pred_set DELETE_COMM)

lemma DELETE_SUBSET: "ALL x xa. SUBSET (DELETE xa x) xa"
  by (import pred_set DELETE_SUBSET)

lemma SUBSET_DELETE: "ALL x xa xb. SUBSET xa (DELETE xb x) = (~ IN x xa & SUBSET xa xb)"
  by (import pred_set SUBSET_DELETE)

lemma SUBSET_INSERT_DELETE: "ALL x s t. SUBSET s (INSERT x t) = SUBSET (DELETE s x) t"
  by (import pred_set SUBSET_INSERT_DELETE)

lemma DIFF_INSERT: "ALL x xa xb. DIFF x (INSERT xb xa) = DIFF (DELETE x xb) xa"
  by (import pred_set DIFF_INSERT)

lemma PSUBSET_INSERT_SUBSET: "ALL x xa. PSUBSET x xa = (EX xb. ~ IN xb x & SUBSET (INSERT xb x) xa)"
  by (import pred_set PSUBSET_INSERT_SUBSET)

lemma PSUBSET_MEMBER: "ALL s t. PSUBSET s t = (SUBSET s t & (EX y. IN y t & ~ IN y s))"
  by (import pred_set PSUBSET_MEMBER)

lemma DELETE_INSERT: "ALL x xa xb.
   DELETE (INSERT x xb) xa =
   (if x = xa then DELETE xb xa else INSERT x (DELETE xb xa))"
  by (import pred_set DELETE_INSERT)

lemma INSERT_DELETE: "ALL x xa. IN x xa --> INSERT x (DELETE xa x) = xa"
  by (import pred_set INSERT_DELETE)

lemma DELETE_INTER: "ALL x xa xb.
   pred_set.INTER (DELETE x xb) xa = DELETE (pred_set.INTER x xa) xb"
  by (import pred_set DELETE_INTER)

lemma DISJOINT_DELETE_SYM: "ALL x xa xb. DISJOINT (DELETE x xb) xa = DISJOINT (DELETE xa xb) x"
  by (import pred_set DISJOINT_DELETE_SYM)

consts
  CHOICE :: "('a => bool) => 'a" 

specification (CHOICE) CHOICE_DEF: "ALL x. x ~= EMPTY --> IN (CHOICE x) x"
  by (import pred_set CHOICE_DEF)

constdefs
  REST :: "('a => bool) => 'a => bool" 
  "REST == %s. DELETE s (CHOICE s)"

lemma REST_DEF: "ALL s. REST s = DELETE s (CHOICE s)"
  by (import pred_set REST_DEF)

lemma CHOICE_NOT_IN_REST: "ALL x. ~ IN (CHOICE x) (REST x)"
  by (import pred_set CHOICE_NOT_IN_REST)

lemma CHOICE_INSERT_REST: "ALL s. s ~= EMPTY --> INSERT (CHOICE s) (REST s) = s"
  by (import pred_set CHOICE_INSERT_REST)

lemma REST_SUBSET: "ALL x. SUBSET (REST x) x"
  by (import pred_set REST_SUBSET)

lemma REST_PSUBSET: "ALL x. x ~= EMPTY --> PSUBSET (REST x) x"
  by (import pred_set REST_PSUBSET)

constdefs
  SING :: "('a => bool) => bool" 
  "SING == %s. EX x. s = INSERT x EMPTY"

lemma SING_DEF: "ALL s. SING s = (EX x. s = INSERT x EMPTY)"
  by (import pred_set SING_DEF)

lemma SING: "ALL x. SING (INSERT x EMPTY)"
  by (import pred_set SING)

lemma IN_SING: "ALL x xa. IN x (INSERT xa EMPTY) = (x = xa)"
  by (import pred_set IN_SING)

lemma NOT_SING_EMPTY: "ALL x. INSERT x EMPTY ~= EMPTY"
  by (import pred_set NOT_SING_EMPTY)

lemma NOT_EMPTY_SING: "ALL x. EMPTY ~= INSERT x EMPTY"
  by (import pred_set NOT_EMPTY_SING)

lemma EQUAL_SING: "ALL x xa. (INSERT x EMPTY = INSERT xa EMPTY) = (x = xa)"
  by (import pred_set EQUAL_SING)

lemma DISJOINT_SING_EMPTY: "ALL x. DISJOINT (INSERT x EMPTY) EMPTY"
  by (import pred_set DISJOINT_SING_EMPTY)

lemma INSERT_SING_UNION: "ALL x xa. INSERT xa x = pred_set.UNION (INSERT xa EMPTY) x"
  by (import pred_set INSERT_SING_UNION)

lemma SING_DELETE: "ALL x. DELETE (INSERT x EMPTY) x = EMPTY"
  by (import pred_set SING_DELETE)

lemma DELETE_EQ_SING: "ALL x xa. IN xa x --> (DELETE x xa = EMPTY) = (x = INSERT xa EMPTY)"
  by (import pred_set DELETE_EQ_SING)

lemma CHOICE_SING: "ALL x. CHOICE (INSERT x EMPTY) = x"
  by (import pred_set CHOICE_SING)

lemma REST_SING: "ALL x. REST (INSERT x EMPTY) = EMPTY"
  by (import pred_set REST_SING)

lemma SING_IFF_EMPTY_REST: "ALL x. SING x = (x ~= EMPTY & REST x = EMPTY)"
  by (import pred_set SING_IFF_EMPTY_REST)

constdefs
  IMAGE :: "('a => 'b) => ('a => bool) => 'b => bool" 
  "IMAGE == %f s. GSPEC (%x. (f x, IN x s))"

lemma IMAGE_DEF: "ALL f s. IMAGE f s = GSPEC (%x. (f x, IN x s))"
  by (import pred_set IMAGE_DEF)

lemma IN_IMAGE: "ALL (x::'b) (xa::'a => bool) xb::'a => 'b.
   IN x (IMAGE xb xa) = (EX xc::'a. x = xb xc & IN xc xa)"
  by (import pred_set IN_IMAGE)

lemma IMAGE_IN: "ALL x xa. IN x xa --> (ALL xb. IN (xb x) (IMAGE xb xa))"
  by (import pred_set IMAGE_IN)

lemma IMAGE_EMPTY: "ALL x. IMAGE x EMPTY = EMPTY"
  by (import pred_set IMAGE_EMPTY)

lemma IMAGE_ID: "ALL x. IMAGE (%x. x) x = x"
  by (import pred_set IMAGE_ID)

lemma IMAGE_COMPOSE: "ALL (x::'b => 'c) (xa::'a => 'b) xb::'a => bool.
   IMAGE (x o xa) xb = IMAGE x (IMAGE xa xb)"
  by (import pred_set IMAGE_COMPOSE)

lemma IMAGE_INSERT: "ALL x xa xb. IMAGE x (INSERT xa xb) = INSERT (x xa) (IMAGE x xb)"
  by (import pred_set IMAGE_INSERT)

lemma IMAGE_EQ_EMPTY: "ALL s x. (IMAGE x s = EMPTY) = (s = EMPTY)"
  by (import pred_set IMAGE_EQ_EMPTY)

lemma IMAGE_DELETE: "ALL f x s. ~ IN x s --> IMAGE f (DELETE s x) = IMAGE f s"
  by (import pred_set IMAGE_DELETE)

lemma IMAGE_UNION: "ALL x xa xb.
   IMAGE x (pred_set.UNION xa xb) = pred_set.UNION (IMAGE x xa) (IMAGE x xb)"
  by (import pred_set IMAGE_UNION)

lemma IMAGE_SUBSET: "ALL x xa. SUBSET x xa --> (ALL xb. SUBSET (IMAGE xb x) (IMAGE xb xa))"
  by (import pred_set IMAGE_SUBSET)

lemma IMAGE_INTER: "ALL f s t.
   SUBSET (IMAGE f (pred_set.INTER s t))
    (pred_set.INTER (IMAGE f s) (IMAGE f t))"
  by (import pred_set IMAGE_INTER)

constdefs
  INJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool" 
  "INJ ==
%f s t.
   (ALL x. IN x s --> IN (f x) t) &
   (ALL x y. IN x s & IN y s --> f x = f y --> x = y)"

lemma INJ_DEF: "ALL f s t.
   INJ f s t =
   ((ALL x. IN x s --> IN (f x) t) &
    (ALL x y. IN x s & IN y s --> f x = f y --> x = y))"
  by (import pred_set INJ_DEF)

lemma INJ_ID: "ALL x. INJ (%x. x) x x"
  by (import pred_set INJ_ID)

lemma INJ_COMPOSE: "ALL x xa xb xc xd. INJ x xb xc & INJ xa xc xd --> INJ (xa o x) xb xd"
  by (import pred_set INJ_COMPOSE)

lemma INJ_EMPTY: "ALL x. All (INJ x EMPTY) & (ALL xa. INJ x xa EMPTY = (xa = EMPTY))"
  by (import pred_set INJ_EMPTY)

constdefs
  SURJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool" 
  "SURJ ==
%f s t.
   (ALL x. IN x s --> IN (f x) t) &
   (ALL x. IN x t --> (EX y. IN y s & f y = x))"

lemma SURJ_DEF: "ALL f s t.
   SURJ f s t =
   ((ALL x. IN x s --> IN (f x) t) &
    (ALL x. IN x t --> (EX y. IN y s & f y = x)))"
  by (import pred_set SURJ_DEF)

lemma SURJ_ID: "ALL x. SURJ (%x. x) x x"
  by (import pred_set SURJ_ID)

lemma SURJ_COMPOSE: "ALL x xa xb xc xd. SURJ x xb xc & SURJ xa xc xd --> SURJ (xa o x) xb xd"
  by (import pred_set SURJ_COMPOSE)

lemma SURJ_EMPTY: "ALL x.
   (ALL xa. SURJ x EMPTY xa = (xa = EMPTY)) &
   (ALL xa. SURJ x xa EMPTY = (xa = EMPTY))"
  by (import pred_set SURJ_EMPTY)

lemma IMAGE_SURJ: "ALL x xa xb. SURJ x xa xb = (IMAGE x xa = xb)"
  by (import pred_set IMAGE_SURJ)

constdefs
  BIJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool" 
  "BIJ == %f s t. INJ f s t & SURJ f s t"

lemma BIJ_DEF: "ALL f s t. BIJ f s t = (INJ f s t & SURJ f s t)"
  by (import pred_set BIJ_DEF)

lemma BIJ_ID: "ALL x. BIJ (%x. x) x x"
  by (import pred_set BIJ_ID)

lemma BIJ_EMPTY: "ALL x.
   (ALL xa. BIJ x EMPTY xa = (xa = EMPTY)) &
   (ALL xa. BIJ x xa EMPTY = (xa = EMPTY))"
  by (import pred_set BIJ_EMPTY)

lemma BIJ_COMPOSE: "ALL x xa xb xc xd. BIJ x xb xc & BIJ xa xc xd --> BIJ (xa o x) xb xd"
  by (import pred_set BIJ_COMPOSE)

consts
  LINV :: "('a => 'b) => ('a => bool) => 'b => 'a" 

specification (LINV) LINV_DEF: "ALL f s t. INJ f s t --> (ALL x. IN x s --> LINV f s (f x) = x)"
  by (import pred_set LINV_DEF)

consts
  RINV :: "('a => 'b) => ('a => bool) => 'b => 'a" 

specification (RINV) RINV_DEF: "ALL f s t. SURJ f s t --> (ALL x. IN x t --> f (RINV f s x) = x)"
  by (import pred_set RINV_DEF)

constdefs
  FINITE :: "('a => bool) => bool" 
  "FINITE ==
%s. ALL P. P EMPTY & (ALL s. P s --> (ALL e. P (INSERT e s))) --> P s"

lemma FINITE_DEF: "ALL s.
   FINITE s =
   (ALL P. P EMPTY & (ALL s. P s --> (ALL e. P (INSERT e s))) --> P s)"
  by (import pred_set FINITE_DEF)

lemma FINITE_EMPTY: "FINITE EMPTY"
  by (import pred_set FINITE_EMPTY)

lemma FINITE_INDUCT: "ALL P.
   P EMPTY &
   (ALL s. FINITE s & P s --> (ALL e. ~ IN e s --> P (INSERT e s))) -->
   (ALL s. FINITE s --> P s)"
  by (import pred_set FINITE_INDUCT)

lemma FINITE_INSERT: "ALL x s. FINITE (INSERT x s) = FINITE s"
  by (import pred_set FINITE_INSERT)

lemma FINITE_DELETE: "ALL x s. FINITE (DELETE s x) = FINITE s"
  by (import pred_set FINITE_DELETE)

lemma FINITE_UNION: "ALL s t. FINITE (pred_set.UNION s t) = (FINITE s & FINITE t)"
  by (import pred_set FINITE_UNION)

lemma INTER_FINITE: "ALL s. FINITE s --> (ALL t. FINITE (pred_set.INTER s t))"
  by (import pred_set INTER_FINITE)

lemma SUBSET_FINITE: "ALL s. FINITE s --> (ALL t. SUBSET t s --> FINITE t)"
  by (import pred_set SUBSET_FINITE)

lemma PSUBSET_FINITE: "ALL x. FINITE x --> (ALL xa. PSUBSET xa x --> FINITE xa)"
  by (import pred_set PSUBSET_FINITE)

lemma FINITE_DIFF: "ALL s. FINITE s --> (ALL t. FINITE (DIFF s t))"
  by (import pred_set FINITE_DIFF)

lemma FINITE_SING: "ALL x. FINITE (INSERT x EMPTY)"
  by (import pred_set FINITE_SING)

lemma SING_FINITE: "ALL x. SING x --> FINITE x"
  by (import pred_set SING_FINITE)

lemma IMAGE_FINITE: "ALL s. FINITE s --> (ALL f. FINITE (IMAGE f s))"
  by (import pred_set IMAGE_FINITE)

consts
  CARD :: "('a => bool) => nat" 

specification (CARD) CARD_DEF: "(op &::bool => bool => bool)
 ((op =::nat => nat => bool)
   ((CARD::('a => bool) => nat) (EMPTY::'a => bool)) (0::nat))
 ((All::(('a => bool) => bool) => bool)
   (%s::'a => bool.
       (op -->::bool => bool => bool) ((FINITE::('a => bool) => bool) s)
        ((All::('a => bool) => bool)
          (%x::'a.
              (op =::nat => nat => bool)
               ((CARD::('a => bool) => nat)
                 ((INSERT::'a => ('a => bool) => 'a => bool) x s))
               ((If::bool => nat => nat => nat)
                 ((IN::'a => ('a => bool) => bool) x s)
                 ((CARD::('a => bool) => nat) s)
                 ((Suc::nat => nat) ((CARD::('a => bool) => nat) s)))))))"
  by (import pred_set CARD_DEF)

lemma CARD_EMPTY: "CARD EMPTY = 0"
  by (import pred_set CARD_EMPTY)

lemma CARD_INSERT: "ALL s.
   FINITE s -->
   (ALL x. CARD (INSERT x s) = (if IN x s then CARD s else Suc (CARD s)))"
  by (import pred_set CARD_INSERT)

lemma CARD_EQ_0: "ALL s. FINITE s --> (CARD s = 0) = (s = EMPTY)"
  by (import pred_set CARD_EQ_0)

lemma CARD_DELETE: "ALL s.
   FINITE s -->
   (ALL x. CARD (DELETE s x) = (if IN x s then CARD s - 1 else CARD s))"
  by (import pred_set CARD_DELETE)

lemma CARD_INTER_LESS_EQ: "ALL s. FINITE s --> (ALL t. CARD (pred_set.INTER s t) <= CARD s)"
  by (import pred_set CARD_INTER_LESS_EQ)

lemma CARD_UNION: "ALL s.
   FINITE s -->
   (ALL t.
       FINITE t -->
       CARD (pred_set.UNION s t) + CARD (pred_set.INTER s t) =
       CARD s + CARD t)"
  by (import pred_set CARD_UNION)

lemma CARD_SUBSET: "ALL s. FINITE s --> (ALL t. SUBSET t s --> CARD t <= CARD s)"
  by (import pred_set CARD_SUBSET)

lemma CARD_PSUBSET: "ALL s. FINITE s --> (ALL t. PSUBSET t s --> CARD t < CARD s)"
  by (import pred_set CARD_PSUBSET)

lemma CARD_SING: "ALL x. CARD (INSERT x EMPTY) = 1"
  by (import pred_set CARD_SING)

lemma SING_IFF_CARD1: "ALL x. SING x = (CARD x = 1 & FINITE x)"
  by (import pred_set SING_IFF_CARD1)

lemma CARD_DIFF: "ALL t.
   FINITE t -->
   (ALL s.
       FINITE s --> CARD (DIFF s t) = CARD s - CARD (pred_set.INTER s t))"
  by (import pred_set CARD_DIFF)

lemma LESS_CARD_DIFF: "ALL t.
   FINITE t -->
   (ALL s. FINITE s --> CARD t < CARD s --> 0 < CARD (DIFF s t))"
  by (import pred_set LESS_CARD_DIFF)

lemma FINITE_COMPLETE_INDUCTION: "ALL P.
   (ALL x. (ALL y. PSUBSET y x --> P y) --> FINITE x --> P x) -->
   (ALL x. FINITE x --> P x)"
  by (import pred_set FINITE_COMPLETE_INDUCTION)

constdefs
  INFINITE :: "('a => bool) => bool" 
  "INFINITE == %s. ~ FINITE s"

lemma INFINITE_DEF: "ALL s. INFINITE s = (~ FINITE s)"
  by (import pred_set INFINITE_DEF)

lemma NOT_IN_FINITE: "(op =::bool => bool => bool)
 ((INFINITE::('a => bool) => bool) (pred_set.UNIV::'a => bool))
 ((All::(('a => bool) => bool) => bool)
   (%s::'a => bool.
       (op -->::bool => bool => bool) ((FINITE::('a => bool) => bool) s)
        ((Ex::('a => bool) => bool)
          (%x::'a.
              (Not::bool => bool) ((IN::'a => ('a => bool) => bool) x s)))))"
  by (import pred_set NOT_IN_FINITE)

lemma INFINITE_INHAB: "ALL x. INFINITE x --> (EX xa. IN xa x)"
  by (import pred_set INFINITE_INHAB)

lemma IMAGE_11_INFINITE: "ALL f.
   (ALL x y. f x = f y --> x = y) -->
   (ALL s. INFINITE s --> INFINITE (IMAGE f s))"
  by (import pred_set IMAGE_11_INFINITE)

lemma INFINITE_SUBSET: "ALL x. INFINITE x --> (ALL xa. SUBSET x xa --> INFINITE xa)"
  by (import pred_set INFINITE_SUBSET)

lemma IN_INFINITE_NOT_FINITE: "ALL x xa. INFINITE x & FINITE xa --> (EX xb. IN xb x & ~ IN xb xa)"
  by (import pred_set IN_INFINITE_NOT_FINITE)

lemma INFINITE_UNIV: "(op =::bool => bool => bool)
 ((INFINITE::('a => bool) => bool) (pred_set.UNIV::'a => bool))
 ((Ex::(('a => 'a) => bool) => bool)
   (%f::'a => 'a.
       (op &::bool => bool => bool)
        ((All::('a => bool) => bool)
          (%x::'a.
              (All::('a => bool) => bool)
               (%y::'a.
                   (op -->::bool => bool => bool)
                    ((op =::'a => 'a => bool) (f x) (f y))
                    ((op =::'a => 'a => bool) x y))))
        ((Ex::('a => bool) => bool)
          (%y::'a.
              (All::('a => bool) => bool)
               (%x::'a.
                   (Not::bool => bool)
                    ((op =::'a => 'a => bool) (f x) y))))))"
  by (import pred_set INFINITE_UNIV)

lemma FINITE_PSUBSET_INFINITE: "ALL x. INFINITE x = (ALL xa. FINITE xa --> SUBSET xa x --> PSUBSET xa x)"
  by (import pred_set FINITE_PSUBSET_INFINITE)

lemma FINITE_PSUBSET_UNIV: "(op =::bool => bool => bool)
 ((INFINITE::('a => bool) => bool) (pred_set.UNIV::'a => bool))
 ((All::(('a => bool) => bool) => bool)
   (%s::'a => bool.
       (op -->::bool => bool => bool) ((FINITE::('a => bool) => bool) s)
        ((PSUBSET::('a => bool) => ('a => bool) => bool) s
          (pred_set.UNIV::'a => bool))))"
  by (import pred_set FINITE_PSUBSET_UNIV)

lemma INFINITE_DIFF_FINITE: "ALL s t. INFINITE s & FINITE t --> DIFF s t ~= EMPTY"
  by (import pred_set INFINITE_DIFF_FINITE)

lemma FINITE_ISO_NUM: "ALL s.
   FINITE s -->
   (EX f. (ALL n m. n < CARD s & m < CARD s --> f n = f m --> n = m) &
          s = GSPEC (%n. (f n, n < CARD s)))"
  by (import pred_set FINITE_ISO_NUM)

lemma FINITE_WEAK_ENUMERATE: "(All::(('a => bool) => bool) => bool)
 (%x::'a => bool.
     (op =::bool => bool => bool) ((FINITE::('a => bool) => bool) x)
      ((Ex::((nat => 'a) => bool) => bool)
        (%f::nat => 'a.
            (Ex::(nat => bool) => bool)
             (%b::nat.
                 (All::('a => bool) => bool)
                  (%e::'a.
                      (op =::bool => bool => bool)
                       ((IN::'a => ('a => bool) => bool) e x)
                       ((Ex::(nat => bool) => bool)
                         (%n::nat.
                             (op &::bool => bool => bool)
                              ((op <::nat => nat => bool) n b)
                              ((op =::'a => 'a => bool) e (f n)))))))))"
  by (import pred_set FINITE_WEAK_ENUMERATE)

constdefs
  BIGUNION :: "(('a => bool) => bool) => 'a => bool" 
  "BIGUNION == %P. GSPEC (%x. (x, EX p. IN p P & IN x p))"

lemma BIGUNION: "ALL P. BIGUNION P = GSPEC (%x. (x, EX p. IN p P & IN x p))"
  by (import pred_set BIGUNION)

lemma IN_BIGUNION: "ALL x xa. IN x (BIGUNION xa) = (EX s. IN x s & IN s xa)"
  by (import pred_set IN_BIGUNION)

lemma BIGUNION_EMPTY: "BIGUNION EMPTY = EMPTY"
  by (import pred_set BIGUNION_EMPTY)

lemma BIGUNION_SING: "ALL x. BIGUNION (INSERT x EMPTY) = x"
  by (import pred_set BIGUNION_SING)

lemma BIGUNION_UNION: "ALL x xa.
   BIGUNION (pred_set.UNION x xa) =
   pred_set.UNION (BIGUNION x) (BIGUNION xa)"
  by (import pred_set BIGUNION_UNION)

lemma DISJOINT_BIGUNION: "(ALL (s::('a => bool) => bool) t::'a => bool.
    DISJOINT (BIGUNION s) t =
    (ALL s'::'a => bool. IN s' s --> DISJOINT s' t)) &
(ALL (x::('a => bool) => bool) xa::'a => bool.
    DISJOINT xa (BIGUNION x) =
    (ALL xb::'a => bool. IN xb x --> DISJOINT xa xb))"
  by (import pred_set DISJOINT_BIGUNION)

lemma BIGUNION_INSERT: "ALL x xa. BIGUNION (INSERT x xa) = pred_set.UNION x (BIGUNION xa)"
  by (import pred_set BIGUNION_INSERT)

lemma BIGUNION_SUBSET: "ALL X P. SUBSET (BIGUNION P) X = (ALL Y. IN Y P --> SUBSET Y X)"
  by (import pred_set BIGUNION_SUBSET)

lemma FINITE_BIGUNION: "ALL x. FINITE x & (ALL s. IN s x --> FINITE s) --> FINITE (BIGUNION x)"
  by (import pred_set FINITE_BIGUNION)

constdefs
  BIGINTER :: "(('a => bool) => bool) => 'a => bool" 
  "BIGINTER == %B. GSPEC (%x. (x, ALL P. IN P B --> IN x P))"

lemma BIGINTER: "ALL B. BIGINTER B = GSPEC (%x. (x, ALL P. IN P B --> IN x P))"
  by (import pred_set BIGINTER)

lemma IN_BIGINTER: "IN x (BIGINTER B) = (ALL P. IN P B --> IN x P)"
  by (import pred_set IN_BIGINTER)

lemma BIGINTER_INSERT: "ALL P B. BIGINTER (INSERT P B) = pred_set.INTER P (BIGINTER B)"
  by (import pred_set BIGINTER_INSERT)

lemma BIGINTER_EMPTY: "BIGINTER EMPTY = pred_set.UNIV"
  by (import pred_set BIGINTER_EMPTY)

lemma BIGINTER_INTER: "ALL x xa. BIGINTER (INSERT x (INSERT xa EMPTY)) = pred_set.INTER x xa"
  by (import pred_set BIGINTER_INTER)

lemma BIGINTER_SING: "ALL x. BIGINTER (INSERT x EMPTY) = x"
  by (import pred_set BIGINTER_SING)

lemma SUBSET_BIGINTER: "ALL X P. SUBSET X (BIGINTER P) = (ALL x. IN x P --> SUBSET X x)"
  by (import pred_set SUBSET_BIGINTER)

lemma DISJOINT_BIGINTER: "ALL x xa xb.
   IN xa xb & DISJOINT xa x -->
   DISJOINT x (BIGINTER xb) & DISJOINT (BIGINTER xb) x"
  by (import pred_set DISJOINT_BIGINTER)

constdefs
  CROSS :: "('a => bool) => ('b => bool) => 'a * 'b => bool" 
  "CROSS == %P Q. GSPEC (%p. (p, IN (fst p) P & IN (snd p) Q))"

lemma CROSS_DEF: "ALL P Q. CROSS P Q = GSPEC (%p. (p, IN (fst p) P & IN (snd p) Q))"
  by (import pred_set CROSS_DEF)

lemma IN_CROSS: "ALL x xa xb. IN xb (CROSS x xa) = (IN (fst xb) x & IN (snd xb) xa)"
  by (import pred_set IN_CROSS)

lemma CROSS_EMPTY: "ALL x. CROSS x EMPTY = EMPTY & CROSS EMPTY x = EMPTY"
  by (import pred_set CROSS_EMPTY)

lemma CROSS_INSERT_LEFT: "ALL x xa xb.
   CROSS (INSERT xb x) xa =
   pred_set.UNION (CROSS (INSERT xb EMPTY) xa) (CROSS x xa)"
  by (import pred_set CROSS_INSERT_LEFT)

lemma CROSS_INSERT_RIGHT: "ALL x xa xb.
   CROSS x (INSERT xb xa) =
   pred_set.UNION (CROSS x (INSERT xb EMPTY)) (CROSS x xa)"
  by (import pred_set CROSS_INSERT_RIGHT)

lemma FINITE_CROSS: "ALL x xa. FINITE x & FINITE xa --> FINITE (CROSS x xa)"
  by (import pred_set FINITE_CROSS)

lemma CROSS_SINGS: "ALL x xa. CROSS (INSERT x EMPTY) (INSERT xa EMPTY) = INSERT (x, xa) EMPTY"
  by (import pred_set CROSS_SINGS)

lemma CARD_SING_CROSS: "ALL x s. FINITE s --> CARD (CROSS (INSERT x EMPTY) s) = CARD s"
  by (import pred_set CARD_SING_CROSS)

lemma CARD_CROSS: "ALL x xa. FINITE x & FINITE xa --> CARD (CROSS x xa) = CARD x * CARD xa"
  by (import pred_set CARD_CROSS)

lemma CROSS_SUBSET: "ALL x xa xb xc.
   SUBSET (CROSS xb xc) (CROSS x xa) =
   (xb = EMPTY | xc = EMPTY | SUBSET xb x & SUBSET xc xa)"
  by (import pred_set CROSS_SUBSET)

lemma FINITE_CROSS_EQ: "ALL P Q. FINITE (CROSS P Q) = (P = EMPTY | Q = EMPTY | FINITE P & FINITE Q)"
  by (import pred_set FINITE_CROSS_EQ)

constdefs
  COMPL :: "('a => bool) => 'a => bool" 
  "COMPL == DIFF pred_set.UNIV"

lemma COMPL_DEF: "ALL P. COMPL P = DIFF pred_set.UNIV P"
  by (import pred_set COMPL_DEF)

lemma IN_COMPL: "ALL x xa. IN x (COMPL xa) = (~ IN x xa)"
  by (import pred_set IN_COMPL)

lemma COMPL_COMPL: "ALL x. COMPL (COMPL x) = x"
  by (import pred_set COMPL_COMPL)

lemma COMPL_CLAUSES: "ALL x.
   pred_set.INTER (COMPL x) x = EMPTY &
   pred_set.UNION (COMPL x) x = pred_set.UNIV"
  by (import pred_set COMPL_CLAUSES)

lemma COMPL_SPLITS: "ALL x xa.
   pred_set.UNION (pred_set.INTER x xa) (pred_set.INTER (COMPL x) xa) = xa"
  by (import pred_set COMPL_SPLITS)

lemma INTER_UNION_COMPL: "ALL x xa. pred_set.INTER x xa = COMPL (pred_set.UNION (COMPL x) (COMPL xa))"
  by (import pred_set INTER_UNION_COMPL)

lemma COMPL_EMPTY: "COMPL EMPTY = pred_set.UNIV"
  by (import pred_set COMPL_EMPTY)

consts
  count :: "nat => nat => bool" 

defs
  count_primdef: "count == %n. GSPEC (%m. (m, m < n))"

lemma count_def: "ALL n. count n = GSPEC (%m. (m, m < n))"
  by (import pred_set count_def)

lemma IN_COUNT: "ALL m n. IN m (count n) = (m < n)"
  by (import pred_set IN_COUNT)

lemma COUNT_ZERO: "count 0 = EMPTY"
  by (import pred_set COUNT_ZERO)

lemma COUNT_SUC: "ALL n. count (Suc n) = INSERT n (count n)"
  by (import pred_set COUNT_SUC)

lemma FINITE_COUNT: "ALL n. FINITE (count n)"
  by (import pred_set FINITE_COUNT)

lemma CARD_COUNT: "ALL n. CARD (count n) = n"
  by (import pred_set CARD_COUNT)

constdefs
  ITSET_tupled :: "('a => 'b => 'b) => ('a => bool) * 'b => 'b" 
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

lemma ITSET_tupled_primitive_def: "ALL f.
   ITSET_tupled f =
   WFREC
    (SOME R.
        WF R &
        (ALL b s.
            FINITE s & s ~= EMPTY --> R (REST s, f (CHOICE s) b) (s, b)))
    (%ITSET_tupled (v, v1).
        if FINITE v
        then if v = EMPTY then v1
             else ITSET_tupled (REST v, f (CHOICE v) v1)
        else ARB)"
  by (import pred_set ITSET_tupled_primitive_def)

constdefs
  ITSET :: "('a => 'b => 'b) => ('a => bool) => 'b => 'b" 
  "ITSET == %f x x1. ITSET_tupled f (x, x1)"

lemma ITSET_curried_def: "ALL f x x1. ITSET f x x1 = ITSET_tupled f (x, x1)"
  by (import pred_set ITSET_curried_def)

lemma ITSET_IND: "ALL P.
   (ALL s b.
       (FINITE s & s ~= EMPTY --> P (REST s) (f (CHOICE s) b)) -->
       P s b) -->
   (ALL v. All (P v))"
  by (import pred_set ITSET_IND)

lemma ITSET_THM: "ALL s f b.
   FINITE s -->
   ITSET f s b =
   (if s = EMPTY then b else ITSET f (REST s) (f (CHOICE s) b))"
  by (import pred_set ITSET_THM)

lemma ITSET_EMPTY: "ALL x xa. ITSET x EMPTY xa = xa"
  by (import pred_set ITSET_EMPTY)

;end_setup

;setup_theory operator

constdefs
  ASSOC :: "('a => 'a => 'a) => bool" 
  "ASSOC == %f. ALL x y z. f x (f y z) = f (f x y) z"

lemma ASSOC_DEF: "ALL f. ASSOC f = (ALL x y z. f x (f y z) = f (f x y) z)"
  by (import operator ASSOC_DEF)

constdefs
  COMM :: "('a => 'a => 'b) => bool" 
  "COMM == %f. ALL x y. f x y = f y x"

lemma COMM_DEF: "ALL f. COMM f = (ALL x y. f x y = f y x)"
  by (import operator COMM_DEF)

constdefs
  FCOMM :: "('a => 'b => 'a) => ('c => 'a => 'a) => bool" 
  "FCOMM == %f g. ALL x y z. g x (f y z) = f (g x y) z"

lemma FCOMM_DEF: "ALL f g. FCOMM f g = (ALL x y z. g x (f y z) = f (g x y) z)"
  by (import operator FCOMM_DEF)

constdefs
  RIGHT_ID :: "('a => 'b => 'a) => 'b => bool" 
  "RIGHT_ID == %f e. ALL x. f x e = x"

lemma RIGHT_ID_DEF: "ALL f e. RIGHT_ID f e = (ALL x. f x e = x)"
  by (import operator RIGHT_ID_DEF)

constdefs
  LEFT_ID :: "('a => 'b => 'b) => 'a => bool" 
  "LEFT_ID == %f e. ALL x. f e x = x"

lemma LEFT_ID_DEF: "ALL f e. LEFT_ID f e = (ALL x. f e x = x)"
  by (import operator LEFT_ID_DEF)

constdefs
  MONOID :: "('a => 'a => 'a) => 'a => bool" 
  "MONOID == %f e. ASSOC f & RIGHT_ID f e & LEFT_ID f e"

lemma MONOID_DEF: "ALL f e. MONOID f e = (ASSOC f & RIGHT_ID f e & LEFT_ID f e)"
  by (import operator MONOID_DEF)

lemma ASSOC_CONJ: "ASSOC op &"
  by (import operator ASSOC_CONJ)

lemma ASSOC_DISJ: "ASSOC op |"
  by (import operator ASSOC_DISJ)

lemma FCOMM_ASSOC: "ALL x. FCOMM x x = ASSOC x"
  by (import operator FCOMM_ASSOC)

lemma MONOID_CONJ_T: "MONOID op & True"
  by (import operator MONOID_CONJ_T)

lemma MONOID_DISJ_F: "MONOID op | False"
  by (import operator MONOID_DISJ_F)

;end_setup

;setup_theory rich_list

consts
  SNOC :: "'a => 'a list => 'a list" 

specification (SNOC) SNOC: "(ALL x::'a. SNOC x [] = [x]) &
(ALL (x::'a) (x'::'a) l::'a list. SNOC x (x' # l) = x' # SNOC x l)"
  by (import rich_list SNOC)

consts
  SCANL :: "('b => 'a => 'b) => 'b => 'a list => 'b list" 

specification (SCANL) SCANL: "(ALL (f::'b => 'a => 'b) e::'b. SCANL f e [] = [e]) &
(ALL (f::'b => 'a => 'b) (e::'b) (x::'a) l::'a list.
    SCANL f e (x # l) = e # SCANL f (f e x) l)"
  by (import rich_list SCANL)

consts
  SCANR :: "('a => 'b => 'b) => 'b => 'a list => 'b list" 

specification (SCANR) SCANR: "(ALL (f::'a => 'b => 'b) e::'b. SCANR f e [] = [e]) &
(ALL (f::'a => 'b => 'b) (e::'b) (x::'a) l::'a list.
    SCANR f e (x # l) = f x (hd (SCANR f e l)) # SCANR f e l)"
  by (import rich_list SCANR)

lemma IS_EL_DEF: "ALL x l. x mem l = list_exists (op = x) l"
  by (import rich_list IS_EL_DEF)

constdefs
  AND_EL :: "bool list => bool" 
  "AND_EL == list_all I"

lemma AND_EL_DEF: "AND_EL = list_all I"
  by (import rich_list AND_EL_DEF)

constdefs
  OR_EL :: "bool list => bool" 
  "OR_EL == list_exists I"

lemma OR_EL_DEF: "OR_EL = list_exists I"
  by (import rich_list OR_EL_DEF)

consts
  FIRSTN :: "nat => 'a list => 'a list" 

specification (FIRSTN) FIRSTN: "(ALL l::'a list. FIRSTN (0::nat) l = []) &
(ALL (n::nat) (x::'a) l::'a list. FIRSTN (Suc n) (x # l) = x # FIRSTN n l)"
  by (import rich_list FIRSTN)

consts
  BUTFIRSTN :: "nat => 'a list => 'a list" 

specification (BUTFIRSTN) BUTFIRSTN: "(ALL l::'a list. BUTFIRSTN (0::nat) l = l) &
(ALL (n::nat) (x::'a) l::'a list. BUTFIRSTN (Suc n) (x # l) = BUTFIRSTN n l)"
  by (import rich_list BUTFIRSTN)

consts
  SEG :: "nat => nat => 'a list => 'a list" 

specification (SEG) SEG: "(ALL (k::nat) l::'a list. SEG (0::nat) k l = []) &
(ALL (m::nat) (x::'a) l::'a list.
    SEG (Suc m) (0::nat) (x # l) = x # SEG m (0::nat) l) &
(ALL (m::nat) (k::nat) (x::'a) l::'a list.
    SEG (Suc m) (Suc k) (x # l) = SEG (Suc m) k l)"
  by (import rich_list SEG)

lemma LAST: "ALL x l. last (SNOC x l) = x"
  by (import rich_list LAST)

lemma BUTLAST: "ALL x l. butlast (SNOC x l) = l"
  by (import rich_list BUTLAST)

consts
  LASTN :: "nat => 'a list => 'a list" 

specification (LASTN) LASTN: "(ALL l::'a list. LASTN (0::nat) l = []) &
(ALL (n::nat) (x::'a) l::'a list.
    LASTN (Suc n) (SNOC x l) = SNOC x (LASTN n l))"
  by (import rich_list LASTN)

consts
  BUTLASTN :: "nat => 'a list => 'a list" 

specification (BUTLASTN) BUTLASTN: "(ALL l::'a list. BUTLASTN (0::nat) l = l) &
(ALL (n::nat) (x::'a) l::'a list.
    BUTLASTN (Suc n) (SNOC x l) = BUTLASTN n l)"
  by (import rich_list BUTLASTN)

lemma EL: "(ALL x::'a list. EL (0::nat) x = hd x) &
(ALL (x::nat) xa::'a list. EL (Suc x) xa = EL x (tl xa))"
  by (import rich_list EL)

consts
  ELL :: "nat => 'a list => 'a" 

specification (ELL) ELL: "(ALL l::'a list. ELL (0::nat) l = last l) &
(ALL (n::nat) l::'a list. ELL (Suc n) l = ELL n (butlast l))"
  by (import rich_list ELL)

consts
  IS_PREFIX :: "'a list => 'a list => bool" 

specification (IS_PREFIX) IS_PREFIX: "(ALL l::'a list. IS_PREFIX l [] = True) &
(ALL (x::'a) l::'a list. IS_PREFIX [] (x # l) = False) &
(ALL (x1::'a) (l1::'a list) (x2::'a) l2::'a list.
    IS_PREFIX (x1 # l1) (x2 # l2) = (x1 = x2 & IS_PREFIX l1 l2))"
  by (import rich_list IS_PREFIX)

lemma SNOC_APPEND: "ALL x l. SNOC x l = l @ [x]"
  by (import rich_list SNOC_APPEND)

lemma REVERSE: "rev [] = [] & (ALL (x::'a) xa::'a list. rev (x # xa) = SNOC x (rev xa))"
  by (import rich_list REVERSE)

lemma REVERSE_SNOC: "ALL x l. rev (SNOC x l) = x # rev l"
  by (import rich_list REVERSE_SNOC)

lemma SNOC_Axiom: "ALL (e::'b) f::'a => 'a list => 'b => 'b.
   EX x::'a list => 'b.
      x [] = e & (ALL (xa::'a) l::'a list. x (SNOC xa l) = f xa l (x l))"
  by (import rich_list SNOC_Axiom)

consts
  IS_SUFFIX :: "'a list => 'a list => bool" 

specification (IS_SUFFIX) IS_SUFFIX: "(ALL l::'a list. IS_SUFFIX l [] = True) &
(ALL (x::'a) l::'a list. IS_SUFFIX [] (SNOC x l) = False) &
(ALL (x1::'a) (l1::'a list) (x2::'a) l2::'a list.
    IS_SUFFIX (SNOC x1 l1) (SNOC x2 l2) = (x1 = x2 & IS_SUFFIX l1 l2))"
  by (import rich_list IS_SUFFIX)

consts
  IS_SUBLIST :: "'a list => 'a list => bool" 

specification (IS_SUBLIST) IS_SUBLIST: "(ALL l::'a list. IS_SUBLIST l [] = True) &
(ALL (x::'a) l::'a list. IS_SUBLIST [] (x # l) = False) &
(ALL (x1::'a) (l1::'a list) (x2::'a) l2::'a list.
    IS_SUBLIST (x1 # l1) (x2 # l2) =
    (x1 = x2 & IS_PREFIX l1 l2 | IS_SUBLIST l1 (x2 # l2)))"
  by (import rich_list IS_SUBLIST)

consts
  SPLITP :: "('a => bool) => 'a list => 'a list * 'a list" 

specification (SPLITP) SPLITP: "(ALL P::'a => bool. SPLITP P [] = ([], [])) &
(ALL (P::'a => bool) (x::'a) l::'a list.
    SPLITP P (x # l) =
    (if P x then ([], x # l) else (x # fst (SPLITP P l), snd (SPLITP P l))))"
  by (import rich_list SPLITP)

constdefs
  PREFIX :: "('a => bool) => 'a list => 'a list" 
  "PREFIX == %P l. fst (SPLITP (Not o P) l)"

lemma PREFIX_DEF: "ALL P l. PREFIX P l = fst (SPLITP (Not o P) l)"
  by (import rich_list PREFIX_DEF)

constdefs
  SUFFIX :: "('a => bool) => 'a list => 'a list" 
  "SUFFIX == %P. foldl (%l' x. if P x then SNOC x l' else []) []"

lemma SUFFIX_DEF: "ALL P l. SUFFIX P l = foldl (%l' x. if P x then SNOC x l' else []) [] l"
  by (import rich_list SUFFIX_DEF)

constdefs
  UNZIP_FST :: "('a * 'b) list => 'a list" 
  "UNZIP_FST == %l. fst (unzip l)"

lemma UNZIP_FST_DEF: "ALL l. UNZIP_FST l = fst (unzip l)"
  by (import rich_list UNZIP_FST_DEF)

constdefs
  UNZIP_SND :: "('a * 'b) list => 'b list" 
  "UNZIP_SND == %l. snd (unzip l)"

lemma UNZIP_SND_DEF: "ALL l. UNZIP_SND l = snd (unzip l)"
  by (import rich_list UNZIP_SND_DEF)

consts
  GENLIST :: "(nat => 'a) => nat => 'a list" 

specification (GENLIST) GENLIST: "(ALL f::nat => 'a. GENLIST f (0::nat) = []) &
(ALL (f::nat => 'a) n::nat. GENLIST f (Suc n) = SNOC (f n) (GENLIST f n))"
  by (import rich_list GENLIST)

consts
  REPLICATE :: "nat => 'a => 'a list" 

specification (REPLICATE) REPLICATE: "(ALL x::'a. REPLICATE (0::nat) x = []) &
(ALL (n::nat) x::'a. REPLICATE (Suc n) x = x # REPLICATE n x)"
  by (import rich_list REPLICATE)

lemma LENGTH_MAP2: "ALL l1 l2.
   length l1 = length l2 -->
   (ALL f.
       length (map2 f l1 l2) = length l1 &
       length (map2 f l1 l2) = length l2)"
  by (import rich_list LENGTH_MAP2)

lemma NULL_EQ_NIL: "ALL l. null l = (l = [])"
  by (import rich_list NULL_EQ_NIL)

lemma LENGTH_EQ: "ALL x y. x = y --> length x = length y"
  by (import rich_list LENGTH_EQ)

lemma LENGTH_NOT_NULL: "ALL l. (0 < length l) = (~ null l)"
  by (import rich_list LENGTH_NOT_NULL)

lemma SNOC_INDUCT: "ALL P. P [] & (ALL l. P l --> (ALL x. P (SNOC x l))) --> All P"
  by (import rich_list SNOC_INDUCT)

lemma SNOC_CASES: "ALL x'. x' = [] | (EX x l. x' = SNOC x l)"
  by (import rich_list SNOC_CASES)

lemma LENGTH_SNOC: "ALL x l. length (SNOC x l) = Suc (length l)"
  by (import rich_list LENGTH_SNOC)

lemma NOT_NIL_SNOC: "ALL x xa. [] ~= SNOC x xa"
  by (import rich_list NOT_NIL_SNOC)

lemma NOT_SNOC_NIL: "ALL x xa. SNOC x xa ~= []"
  by (import rich_list NOT_SNOC_NIL)

lemma SNOC_11: "ALL x l x' l'. (SNOC x l = SNOC x' l') = (x = x' & l = l')"
  by (import rich_list SNOC_11)

lemma SNOC_EQ_LENGTH_EQ: "ALL x1 l1 x2 l2. SNOC x1 l1 = SNOC x2 l2 --> length l1 = length l2"
  by (import rich_list SNOC_EQ_LENGTH_EQ)

lemma SNOC_REVERSE_CONS: "ALL x xa. SNOC x xa = rev (x # rev xa)"
  by (import rich_list SNOC_REVERSE_CONS)

lemma MAP_SNOC: "ALL x xa xb. map x (SNOC xa xb) = SNOC (x xa) (map x xb)"
  by (import rich_list MAP_SNOC)

lemma FOLDR_SNOC: "ALL f e x l. foldr f (SNOC x l) e = foldr f l (f x e)"
  by (import rich_list FOLDR_SNOC)

lemma FOLDL_SNOC: "ALL (f::'b => 'a => 'b) (e::'b) (x::'a) l::'a list.
   foldl f e (SNOC x l) = f (foldl f e l) x"
  by (import rich_list FOLDL_SNOC)

lemma FOLDR_FOLDL: "ALL f e. MONOID f e --> (ALL l. foldr f l e = foldl f e l)"
  by (import rich_list FOLDR_FOLDL)

lemma LENGTH_FOLDR: "ALL l. length l = foldr (%x. Suc) l 0"
  by (import rich_list LENGTH_FOLDR)

lemma LENGTH_FOLDL: "ALL l. length l = foldl (%l' x. Suc l') 0 l"
  by (import rich_list LENGTH_FOLDL)

lemma MAP_FOLDR: "ALL f l. map f l = foldr (%x. op # (f x)) l []"
  by (import rich_list MAP_FOLDR)

lemma MAP_FOLDL: "ALL f l. map f l = foldl (%l' x. SNOC (f x) l') [] l"
  by (import rich_list MAP_FOLDL)

lemma MAP_o: "ALL (f::'b => 'c) g::'a => 'b. map (f o g) = map f o map g"
  by (import rich_list MAP_o)

lemma FILTER_FOLDR: "ALL P l. filter P l = foldr (%x l'. if P x then x # l' else l') l []"
  by (import rich_list FILTER_FOLDR)

lemma FILTER_SNOC: "ALL P x l.
   filter P (SNOC x l) = (if P x then SNOC x (filter P l) else filter P l)"
  by (import rich_list FILTER_SNOC)

lemma FILTER_FOLDL: "ALL P l. filter P l = foldl (%l' x. if P x then SNOC x l' else l') [] l"
  by (import rich_list FILTER_FOLDL)

lemma FILTER_COMM: "ALL f1 f2 l. filter f1 (filter f2 l) = filter f2 (filter f1 l)"
  by (import rich_list FILTER_COMM)

lemma FILTER_IDEM: "ALL f l. filter f (filter f l) = filter f l"
  by (import rich_list FILTER_IDEM)

lemma FILTER_MAP: "ALL (f1::'b => bool) (f2::'a => 'b) l::'a list.
   filter f1 (map f2 l) = map f2 (filter (f1 o f2) l)"
  by (import rich_list FILTER_MAP)

lemma LENGTH_SEG: "ALL n k l. n + k <= length l --> length (SEG n k l) = n"
  by (import rich_list LENGTH_SEG)

lemma APPEND_NIL: "(ALL l::'a list. l @ [] = l) & (ALL x::'a list. [] @ x = x)"
  by (import rich_list APPEND_NIL)

lemma APPEND_SNOC: "ALL l1 x l2. l1 @ SNOC x l2 = SNOC x (l1 @ l2)"
  by (import rich_list APPEND_SNOC)

lemma APPEND_FOLDR: "ALL l1 l2. l1 @ l2 = foldr op # l1 l2"
  by (import rich_list APPEND_FOLDR)

lemma APPEND_FOLDL: "ALL l1 l2. l1 @ l2 = foldl (%l' x. SNOC x l') l1 l2"
  by (import rich_list APPEND_FOLDL)

lemma CONS_APPEND: "ALL x l. x # l = [x] @ l"
  by (import rich_list CONS_APPEND)

lemma ASSOC_APPEND: "ASSOC op @"
  by (import rich_list ASSOC_APPEND)

lemma MONOID_APPEND_NIL: "MONOID op @ []"
  by (import rich_list MONOID_APPEND_NIL)

lemma APPEND_LENGTH_EQ: "ALL l1 l1'.
   length l1 = length l1' -->
   (ALL l2 l2'.
       length l2 = length l2' -->
       (l1 @ l2 = l1' @ l2') = (l1 = l1' & l2 = l2'))"
  by (import rich_list APPEND_LENGTH_EQ)

lemma FLAT_SNOC: "ALL x l. concat (SNOC x l) = concat l @ x"
  by (import rich_list FLAT_SNOC)

lemma FLAT_FOLDR: "ALL l. concat l = foldr op @ l []"
  by (import rich_list FLAT_FOLDR)

lemma FLAT_FOLDL: "ALL l. concat l = foldl op @ [] l"
  by (import rich_list FLAT_FOLDL)

lemma LENGTH_FLAT: "ALL l. length (concat l) = sum (map size l)"
  by (import rich_list LENGTH_FLAT)

lemma REVERSE_FOLDR: "ALL l. rev l = foldr SNOC l []"
  by (import rich_list REVERSE_FOLDR)

lemma REVERSE_FOLDL: "ALL l. rev l = foldl (%l' x. x # l') [] l"
  by (import rich_list REVERSE_FOLDL)

lemma ALL_EL_SNOC: "ALL P x l. list_all P (SNOC x l) = (list_all P l & P x)"
  by (import rich_list ALL_EL_SNOC)

lemma ALL_EL_MAP: "ALL (P::'b => bool) (f::'a => 'b) l::'a list.
   list_all P (map f l) = list_all (P o f) l"
  by (import rich_list ALL_EL_MAP)

lemma SOME_EL_SNOC: "ALL P x l. list_exists P (SNOC x l) = (P x | list_exists P l)"
  by (import rich_list SOME_EL_SNOC)

lemma IS_EL_SNOC: "ALL y x l. y mem SNOC x l = (y = x | y mem l)"
  by (import rich_list IS_EL_SNOC)

lemma SUM_SNOC: "ALL x l. sum (SNOC x l) = sum l + x"
  by (import rich_list SUM_SNOC)

lemma SUM_FOLDL: "ALL l. sum l = foldl op + 0 l"
  by (import rich_list SUM_FOLDL)

lemma IS_PREFIX_APPEND: "ALL l1 l2. IS_PREFIX l1 l2 = (EX l. l1 = l2 @ l)"
  by (import rich_list IS_PREFIX_APPEND)

lemma IS_SUFFIX_APPEND: "ALL l1 l2. IS_SUFFIX l1 l2 = (EX l. l1 = l @ l2)"
  by (import rich_list IS_SUFFIX_APPEND)

lemma IS_SUBLIST_APPEND: "ALL l1 l2. IS_SUBLIST l1 l2 = (EX l l'. l1 = l @ l2 @ l')"
  by (import rich_list IS_SUBLIST_APPEND)

lemma IS_PREFIX_IS_SUBLIST: "ALL l1 l2. IS_PREFIX l1 l2 --> IS_SUBLIST l1 l2"
  by (import rich_list IS_PREFIX_IS_SUBLIST)

lemma IS_SUFFIX_IS_SUBLIST: "ALL l1 l2. IS_SUFFIX l1 l2 --> IS_SUBLIST l1 l2"
  by (import rich_list IS_SUFFIX_IS_SUBLIST)

lemma IS_PREFIX_REVERSE: "ALL l1 l2. IS_PREFIX (rev l1) (rev l2) = IS_SUFFIX l1 l2"
  by (import rich_list IS_PREFIX_REVERSE)

lemma IS_SUFFIX_REVERSE: "ALL l2 l1. IS_SUFFIX (rev l1) (rev l2) = IS_PREFIX l1 l2"
  by (import rich_list IS_SUFFIX_REVERSE)

lemma IS_SUBLIST_REVERSE: "ALL l1 l2. IS_SUBLIST (rev l1) (rev l2) = IS_SUBLIST l1 l2"
  by (import rich_list IS_SUBLIST_REVERSE)

lemma PREFIX_FOLDR: "ALL P x. PREFIX P x = foldr (%x l'. if P x then x # l' else []) x []"
  by (import rich_list PREFIX_FOLDR)

lemma PREFIX: "(ALL x::'a => bool. PREFIX x [] = []) &
(ALL (x::'a => bool) (xa::'a) xb::'a list.
    PREFIX x (xa # xb) = (if x xa then xa # PREFIX x xb else []))"
  by (import rich_list PREFIX)

lemma IS_PREFIX_PREFIX: "ALL P l. IS_PREFIX l (PREFIX P l)"
  by (import rich_list IS_PREFIX_PREFIX)

lemma LENGTH_SCANL: "ALL (f::'b => 'a => 'b) (e::'b) l::'a list.
   length (SCANL f e l) = Suc (length l)"
  by (import rich_list LENGTH_SCANL)

lemma LENGTH_SCANR: "ALL f e l. length (SCANR f e l) = Suc (length l)"
  by (import rich_list LENGTH_SCANR)

lemma COMM_MONOID_FOLDL: "ALL x.
   COMM x -->
   (ALL xa. MONOID x xa --> (ALL e l. foldl x e l = x e (foldl x xa l)))"
  by (import rich_list COMM_MONOID_FOLDL)

lemma COMM_MONOID_FOLDR: "ALL x.
   COMM x -->
   (ALL xa. MONOID x xa --> (ALL e l. foldr x l e = x e (foldr x l xa)))"
  by (import rich_list COMM_MONOID_FOLDR)

lemma FCOMM_FOLDR_APPEND: "ALL x xa.
   FCOMM x xa -->
   (ALL xb.
       LEFT_ID x xb -->
       (ALL l1 l2.
           foldr xa (l1 @ l2) xb = x (foldr xa l1 xb) (foldr xa l2 xb)))"
  by (import rich_list FCOMM_FOLDR_APPEND)

lemma FCOMM_FOLDL_APPEND: "ALL x xa.
   FCOMM x xa -->
   (ALL xb.
       RIGHT_ID xa xb -->
       (ALL l1 l2.
           foldl x xb (l1 @ l2) = xa (foldl x xb l1) (foldl x xb l2)))"
  by (import rich_list FCOMM_FOLDL_APPEND)

lemma FOLDL_SINGLE: "ALL x xa xb. foldl x xa [xb] = x xa xb"
  by (import rich_list FOLDL_SINGLE)

lemma FOLDR_SINGLE: "ALL x xa xb. foldr x [xb] xa = x xb xa"
  by (import rich_list FOLDR_SINGLE)

lemma FOLDR_CONS_NIL: "ALL l. foldr op # l [] = l"
  by (import rich_list FOLDR_CONS_NIL)

lemma FOLDL_SNOC_NIL: "ALL l. foldl (%xs x. SNOC x xs) [] l = l"
  by (import rich_list FOLDL_SNOC_NIL)

lemma FOLDR_REVERSE: "ALL x xa xb. foldr x (rev xb) xa = foldl (%xa y. x y xa) xa xb"
  by (import rich_list FOLDR_REVERSE)

lemma FOLDL_REVERSE: "ALL x xa xb. foldl x xa (rev xb) = foldr (%xa y. x y xa) xb xa"
  by (import rich_list FOLDL_REVERSE)

lemma FOLDR_MAP: "ALL (f::'a => 'a => 'a) (e::'a) (g::'b => 'a) l::'b list.
   foldr f (map g l) e = foldr (%x::'b. f (g x)) l e"
  by (import rich_list FOLDR_MAP)

lemma FOLDL_MAP: "ALL (f::'a => 'a => 'a) (e::'a) (g::'b => 'a) l::'b list.
   foldl f e (map g l) = foldl (%(x::'a) y::'b. f x (g y)) e l"
  by (import rich_list FOLDL_MAP)

lemma ALL_EL_FOLDR: "ALL P l. list_all P l = foldr (%x. op & (P x)) l True"
  by (import rich_list ALL_EL_FOLDR)

lemma ALL_EL_FOLDL: "ALL P l. list_all P l = foldl (%l' x. l' & P x) True l"
  by (import rich_list ALL_EL_FOLDL)

lemma SOME_EL_FOLDR: "ALL P l. list_exists P l = foldr (%x. op | (P x)) l False"
  by (import rich_list SOME_EL_FOLDR)

lemma SOME_EL_FOLDL: "ALL P l. list_exists P l = foldl (%l' x. l' | P x) False l"
  by (import rich_list SOME_EL_FOLDL)

lemma ALL_EL_FOLDR_MAP: "ALL x xa. list_all x xa = foldr op & (map x xa) True"
  by (import rich_list ALL_EL_FOLDR_MAP)

lemma ALL_EL_FOLDL_MAP: "ALL x xa. list_all x xa = foldl op & True (map x xa)"
  by (import rich_list ALL_EL_FOLDL_MAP)

lemma SOME_EL_FOLDR_MAP: "ALL x xa. list_exists x xa = foldr op | (map x xa) False"
  by (import rich_list SOME_EL_FOLDR_MAP)

lemma SOME_EL_FOLDL_MAP: "ALL x xa. list_exists x xa = foldl op | False (map x xa)"
  by (import rich_list SOME_EL_FOLDL_MAP)

lemma FOLDR_FILTER: "ALL (f::'a => 'a => 'a) (e::'a) (P::'a => bool) l::'a list.
   foldr f (filter P l) e =
   foldr (%(x::'a) y::'a. if P x then f x y else y) l e"
  by (import rich_list FOLDR_FILTER)

lemma FOLDL_FILTER: "ALL (f::'a => 'a => 'a) (e::'a) (P::'a => bool) l::'a list.
   foldl f e (filter P l) =
   foldl (%(x::'a) y::'a. if P y then f x y else x) e l"
  by (import rich_list FOLDL_FILTER)

lemma ASSOC_FOLDR_FLAT: "ALL f.
   ASSOC f -->
   (ALL e.
       LEFT_ID f e -->
       (ALL l. foldr f (concat l) e = foldr f (map (FOLDR f e) l) e))"
  by (import rich_list ASSOC_FOLDR_FLAT)

lemma ASSOC_FOLDL_FLAT: "ALL f.
   ASSOC f -->
   (ALL e.
       RIGHT_ID f e -->
       (ALL l. foldl f e (concat l) = foldl f e (map (foldl f e) l)))"
  by (import rich_list ASSOC_FOLDL_FLAT)

lemma SOME_EL_MAP: "ALL (P::'b => bool) (f::'a => 'b) l::'a list.
   list_exists P (map f l) = list_exists (P o f) l"
  by (import rich_list SOME_EL_MAP)

lemma SOME_EL_DISJ: "ALL P Q l.
   list_exists (%x. P x | Q x) l = (list_exists P l | list_exists Q l)"
  by (import rich_list SOME_EL_DISJ)

lemma IS_EL_FOLDR: "ALL x xa. x mem xa = foldr (%xa. op | (x = xa)) xa False"
  by (import rich_list IS_EL_FOLDR)

lemma IS_EL_FOLDL: "ALL x xa. x mem xa = foldl (%l' xa. l' | x = xa) False xa"
  by (import rich_list IS_EL_FOLDL)

lemma NULL_FOLDR: "ALL l. null l = foldr (%x l'. False) l True"
  by (import rich_list NULL_FOLDR)

lemma NULL_FOLDL: "ALL l. null l = foldl (%x l'. False) True l"
  by (import rich_list NULL_FOLDL)

lemma FILTER_REVERSE: "ALL P l. filter P (rev l) = rev (filter P l)"
  by (import rich_list FILTER_REVERSE)

lemma SEG_LENGTH_ID: "ALL l. SEG (length l) 0 l = l"
  by (import rich_list SEG_LENGTH_ID)

lemma SEG_SUC_CONS: "ALL m n l x. SEG m (Suc n) (x # l) = SEG m n l"
  by (import rich_list SEG_SUC_CONS)

lemma SEG_0_SNOC: "ALL m l x. m <= length l --> SEG m 0 (SNOC x l) = SEG m 0 l"
  by (import rich_list SEG_0_SNOC)

lemma BUTLASTN_SEG: "ALL n l. n <= length l --> BUTLASTN n l = SEG (length l - n) 0 l"
  by (import rich_list BUTLASTN_SEG)

lemma LASTN_CONS: "ALL n l. n <= length l --> (ALL x. LASTN n (x # l) = LASTN n l)"
  by (import rich_list LASTN_CONS)

lemma LENGTH_LASTN: "ALL n l. n <= length l --> length (LASTN n l) = n"
  by (import rich_list LENGTH_LASTN)

lemma LASTN_LENGTH_ID: "ALL l. LASTN (length l) l = l"
  by (import rich_list LASTN_LENGTH_ID)

lemma LASTN_LASTN: "ALL l n m. m <= length l --> n <= m --> LASTN n (LASTN m l) = LASTN n l"
  by (import rich_list LASTN_LASTN)

lemma FIRSTN_LENGTH_ID: "ALL l. FIRSTN (length l) l = l"
  by (import rich_list FIRSTN_LENGTH_ID)

lemma FIRSTN_SNOC: "ALL n l. n <= length l --> (ALL x. FIRSTN n (SNOC x l) = FIRSTN n l)"
  by (import rich_list FIRSTN_SNOC)

lemma BUTLASTN_LENGTH_NIL: "ALL l. BUTLASTN (length l) l = []"
  by (import rich_list BUTLASTN_LENGTH_NIL)

lemma BUTLASTN_SUC_BUTLAST: "ALL n l. n < length l --> BUTLASTN (Suc n) l = BUTLASTN n (butlast l)"
  by (import rich_list BUTLASTN_SUC_BUTLAST)

lemma BUTLASTN_BUTLAST: "ALL n l. n < length l --> BUTLASTN n (butlast l) = butlast (BUTLASTN n l)"
  by (import rich_list BUTLASTN_BUTLAST)

lemma LENGTH_BUTLASTN: "ALL n l. n <= length l --> length (BUTLASTN n l) = length l - n"
  by (import rich_list LENGTH_BUTLASTN)

lemma BUTLASTN_BUTLASTN: "ALL m n l.
   n + m <= length l --> BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l"
  by (import rich_list BUTLASTN_BUTLASTN)

lemma APPEND_BUTLASTN_LASTN: "ALL n l. n <= length l --> BUTLASTN n l @ LASTN n l = l"
  by (import rich_list APPEND_BUTLASTN_LASTN)

lemma APPEND_FIRSTN_LASTN: "ALL m n l. m + n = length l --> FIRSTN n l @ LASTN m l = l"
  by (import rich_list APPEND_FIRSTN_LASTN)

lemma BUTLASTN_APPEND2: "ALL n l1 l2. n <= length l2 --> BUTLASTN n (l1 @ l2) = l1 @ BUTLASTN n l2"
  by (import rich_list BUTLASTN_APPEND2)

lemma BUTLASTN_LENGTH_APPEND: "ALL l2 l1. BUTLASTN (length l2) (l1 @ l2) = l1"
  by (import rich_list BUTLASTN_LENGTH_APPEND)

lemma LASTN_LENGTH_APPEND: "ALL l2 l1. LASTN (length l2) (l1 @ l2) = l2"
  by (import rich_list LASTN_LENGTH_APPEND)

lemma BUTLASTN_CONS: "ALL n l. n <= length l --> (ALL x. BUTLASTN n (x # l) = x # BUTLASTN n l)"
  by (import rich_list BUTLASTN_CONS)

lemma BUTLASTN_LENGTH_CONS: "ALL l x. BUTLASTN (length l) (x # l) = [x]"
  by (import rich_list BUTLASTN_LENGTH_CONS)

lemma LAST_LASTN_LAST: "ALL n l. n <= length l --> 0 < n --> last (LASTN n l) = last l"
  by (import rich_list LAST_LASTN_LAST)

lemma BUTLASTN_LASTN_NIL: "ALL n l. n <= length l --> BUTLASTN n (LASTN n l) = []"
  by (import rich_list BUTLASTN_LASTN_NIL)

lemma LASTN_BUTLASTN: "ALL n m l.
   n + m <= length l -->
   LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l)"
  by (import rich_list LASTN_BUTLASTN)

lemma BUTLASTN_LASTN: "ALL m n l.
   m <= n & n <= length l -->
   BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l)"
  by (import rich_list BUTLASTN_LASTN)

lemma LASTN_1: "ALL l. l ~= [] --> LASTN 1 l = [last l]"
  by (import rich_list LASTN_1)

lemma BUTLASTN_1: "ALL l. l ~= [] --> BUTLASTN 1 l = butlast l"
  by (import rich_list BUTLASTN_1)

lemma BUTLASTN_APPEND1: "ALL l2 n.
   length l2 <= n -->
   (ALL l1. BUTLASTN n (l1 @ l2) = BUTLASTN (n - length l2) l1)"
  by (import rich_list BUTLASTN_APPEND1)

lemma LASTN_APPEND2: "ALL n l2. n <= length l2 --> (ALL l1. LASTN n (l1 @ l2) = LASTN n l2)"
  by (import rich_list LASTN_APPEND2)

lemma LASTN_APPEND1: "ALL l2 n.
   length l2 <= n -->
   (ALL l1. LASTN n (l1 @ l2) = LASTN (n - length l2) l1 @ l2)"
  by (import rich_list LASTN_APPEND1)

lemma LASTN_MAP: "ALL n l. n <= length l --> (ALL f. LASTN n (map f l) = map f (LASTN n l))"
  by (import rich_list LASTN_MAP)

lemma BUTLASTN_MAP: "ALL n l.
   n <= length l --> (ALL f. BUTLASTN n (map f l) = map f (BUTLASTN n l))"
  by (import rich_list BUTLASTN_MAP)

lemma ALL_EL_LASTN: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (All::('a list => bool) => bool)
      (%l::'a list.
          (op -->::bool => bool => bool)
           ((list_all::('a => bool) => 'a list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m ((size::'a list => nat) l))
                  ((list_all::('a => bool) => 'a list => bool) P
                    ((LASTN::nat => 'a list => 'a list) m l))))))"
  by (import rich_list ALL_EL_LASTN)

lemma ALL_EL_BUTLASTN: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (All::('a list => bool) => bool)
      (%l::'a list.
          (op -->::bool => bool => bool)
           ((list_all::('a => bool) => 'a list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m ((size::'a list => nat) l))
                  ((list_all::('a => bool) => 'a list => bool) P
                    ((BUTLASTN::nat => 'a list => 'a list) m l))))))"
  by (import rich_list ALL_EL_BUTLASTN)

lemma LENGTH_FIRSTN: "ALL n l. n <= length l --> length (FIRSTN n l) = n"
  by (import rich_list LENGTH_FIRSTN)

lemma FIRSTN_FIRSTN: "(All::(nat => bool) => bool)
 (%m::nat.
     (All::('a list => bool) => bool)
      (%l::'a list.
          (op -->::bool => bool => bool)
           ((op <=::nat => nat => bool) m ((size::'a list => nat) l))
           ((All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) n m)
                  ((op =::'a list => 'a list => bool)
                    ((FIRSTN::nat => 'a list => 'a list) n
                      ((FIRSTN::nat => 'a list => 'a list) m l))
                    ((FIRSTN::nat => 'a list => 'a list) n l))))))"
  by (import rich_list FIRSTN_FIRSTN)

lemma LENGTH_BUTFIRSTN: "ALL n l. n <= length l --> length (BUTFIRSTN n l) = length l - n"
  by (import rich_list LENGTH_BUTFIRSTN)

lemma BUTFIRSTN_LENGTH_NIL: "ALL l. BUTFIRSTN (length l) l = []"
  by (import rich_list BUTFIRSTN_LENGTH_NIL)

lemma BUTFIRSTN_APPEND1: "ALL n l1.
   n <= length l1 --> (ALL l2. BUTFIRSTN n (l1 @ l2) = BUTFIRSTN n l1 @ l2)"
  by (import rich_list BUTFIRSTN_APPEND1)

lemma BUTFIRSTN_APPEND2: "ALL l1 n.
   length l1 <= n -->
   (ALL l2. BUTFIRSTN n (l1 @ l2) = BUTFIRSTN (n - length l1) l2)"
  by (import rich_list BUTFIRSTN_APPEND2)

lemma BUTFIRSTN_BUTFIRSTN: "ALL n m l.
   n + m <= length l --> BUTFIRSTN n (BUTFIRSTN m l) = BUTFIRSTN (n + m) l"
  by (import rich_list BUTFIRSTN_BUTFIRSTN)

lemma APPEND_FIRSTN_BUTFIRSTN: "ALL n l. n <= length l --> FIRSTN n l @ BUTFIRSTN n l = l"
  by (import rich_list APPEND_FIRSTN_BUTFIRSTN)

lemma LASTN_SEG: "ALL n l. n <= length l --> LASTN n l = SEG n (length l - n) l"
  by (import rich_list LASTN_SEG)

lemma FIRSTN_SEG: "ALL n l. n <= length l --> FIRSTN n l = SEG n 0 l"
  by (import rich_list FIRSTN_SEG)

lemma BUTFIRSTN_SEG: "ALL n l. n <= length l --> BUTFIRSTN n l = SEG (length l - n) n l"
  by (import rich_list BUTFIRSTN_SEG)

lemma BUTFIRSTN_SNOC: "ALL n l.
   n <= length l -->
   (ALL x. BUTFIRSTN n (SNOC x l) = SNOC x (BUTFIRSTN n l))"
  by (import rich_list BUTFIRSTN_SNOC)

lemma APPEND_BUTLASTN_BUTFIRSTN: "ALL m n l. m + n = length l --> BUTLASTN m l @ BUTFIRSTN n l = l"
  by (import rich_list APPEND_BUTLASTN_BUTFIRSTN)

lemma SEG_SEG: "ALL n1 m1 n2 m2 l.
   n1 + m1 <= length l & n2 + m2 <= n1 -->
   SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l"
  by (import rich_list SEG_SEG)

lemma SEG_APPEND1: "ALL n m l1. n + m <= length l1 --> (ALL l2. SEG n m (l1 @ l2) = SEG n m l1)"
  by (import rich_list SEG_APPEND1)

lemma SEG_APPEND2: "ALL l1 m n l2.
   length l1 <= m & n <= length l2 -->
   SEG n m (l1 @ l2) = SEG n (m - length l1) l2"
  by (import rich_list SEG_APPEND2)

lemma SEG_FIRSTN_BUTFISTN: "ALL n m l. n + m <= length l --> SEG n m l = FIRSTN n (BUTFIRSTN m l)"
  by (import rich_list SEG_FIRSTN_BUTFISTN)

lemma SEG_APPEND: "ALL m l1 n l2.
   m < length l1 & length l1 <= n + m & n + m <= length l1 + length l2 -->
   SEG n m (l1 @ l2) =
   SEG (length l1 - m) m l1 @ SEG (n + m - length l1) 0 l2"
  by (import rich_list SEG_APPEND)

lemma SEG_LENGTH_SNOC: "ALL x xa. SEG 1 (length x) (SNOC xa x) = [xa]"
  by (import rich_list SEG_LENGTH_SNOC)

lemma SEG_SNOC: "ALL n m l. n + m <= length l --> (ALL x. SEG n m (SNOC x l) = SEG n m l)"
  by (import rich_list SEG_SNOC)

lemma ELL_SEG: "ALL n l. n < length l --> ELL n l = hd (SEG 1 (PRE (length l - n)) l)"
  by (import rich_list ELL_SEG)

lemma SNOC_FOLDR: "ALL x l. SNOC x l = foldr op # l [x]"
  by (import rich_list SNOC_FOLDR)

lemma IS_EL_FOLDR_MAP: "ALL x xa. x mem xa = foldr op | (map (op = x) xa) False"
  by (import rich_list IS_EL_FOLDR_MAP)

lemma IS_EL_FOLDL_MAP: "ALL x xa. x mem xa = foldl op | False (map (op = x) xa)"
  by (import rich_list IS_EL_FOLDL_MAP)

lemma FILTER_FILTER: "ALL P Q l. filter P (filter Q l) = [x:l. P x & Q x]"
  by (import rich_list FILTER_FILTER)

lemma FCOMM_FOLDR_FLAT: "ALL g f.
   FCOMM g f -->
   (ALL e.
       LEFT_ID g e -->
       (ALL l. foldr f (concat l) e = foldr g (map (FOLDR f e) l) e))"
  by (import rich_list FCOMM_FOLDR_FLAT)

lemma FCOMM_FOLDL_FLAT: "ALL f g.
   FCOMM f g -->
   (ALL e.
       RIGHT_ID g e -->
       (ALL l. foldl f e (concat l) = foldl g e (map (foldl f e) l)))"
  by (import rich_list FCOMM_FOLDL_FLAT)

lemma FOLDR_MAP_REVERSE: "ALL f::'a => 'a => 'a.
   (ALL (a::'a) (b::'a) c::'a. f a (f b c) = f b (f a c)) -->
   (ALL (e::'a) (g::'b => 'a) l::'b list.
       foldr f (map g (rev l)) e = foldr f (map g l) e)"
  by (import rich_list FOLDR_MAP_REVERSE)

lemma FOLDR_FILTER_REVERSE: "ALL f::'a => 'a => 'a.
   (ALL (a::'a) (b::'a) c::'a. f a (f b c) = f b (f a c)) -->
   (ALL (e::'a) (P::'a => bool) l::'a list.
       foldr f (filter P (rev l)) e = foldr f (filter P l) e)"
  by (import rich_list FOLDR_FILTER_REVERSE)

lemma COMM_ASSOC_FOLDR_REVERSE: "ALL f. COMM f --> ASSOC f --> (ALL e l. foldr f (rev l) e = foldr f l e)"
  by (import rich_list COMM_ASSOC_FOLDR_REVERSE)

lemma COMM_ASSOC_FOLDL_REVERSE: "ALL f. COMM f --> ASSOC f --> (ALL e l. foldl f e (rev l) = foldl f e l)"
  by (import rich_list COMM_ASSOC_FOLDL_REVERSE)

lemma ELL_LAST: "ALL l. ~ null l --> ELL 0 l = last l"
  by (import rich_list ELL_LAST)

lemma ELL_0_SNOC: "ALL l x. ELL 0 (SNOC x l) = x"
  by (import rich_list ELL_0_SNOC)

lemma ELL_SNOC: "ALL n. 0 < n --> (ALL x l. ELL n (SNOC x l) = ELL (PRE n) l)"
  by (import rich_list ELL_SNOC)

lemma ELL_SUC_SNOC: "ALL n x xa. ELL (Suc n) (SNOC x xa) = ELL n xa"
  by (import rich_list ELL_SUC_SNOC)

lemma ELL_CONS: "ALL n l. n < length l --> (ALL x. ELL n (x # l) = ELL n l)"
  by (import rich_list ELL_CONS)

lemma ELL_LENGTH_CONS: "ALL l x. ELL (length l) (x # l) = x"
  by (import rich_list ELL_LENGTH_CONS)

lemma ELL_LENGTH_SNOC: "ALL l x. ELL (length l) (SNOC x l) = (if null l then x else hd l)"
  by (import rich_list ELL_LENGTH_SNOC)

lemma ELL_APPEND2: "ALL n l2. n < length l2 --> (ALL l1. ELL n (l1 @ l2) = ELL n l2)"
  by (import rich_list ELL_APPEND2)

lemma ELL_APPEND1: "ALL l2 n.
   length l2 <= n --> (ALL l1. ELL n (l1 @ l2) = ELL (n - length l2) l1)"
  by (import rich_list ELL_APPEND1)

lemma ELL_PRE_LENGTH: "ALL l. l ~= [] --> ELL (PRE (length l)) l = hd l"
  by (import rich_list ELL_PRE_LENGTH)

lemma EL_LENGTH_SNOC: "ALL l x. EL (length l) (SNOC x l) = x"
  by (import rich_list EL_LENGTH_SNOC)

lemma EL_PRE_LENGTH: "ALL l. l ~= [] --> EL (PRE (length l)) l = last l"
  by (import rich_list EL_PRE_LENGTH)

lemma EL_SNOC: "ALL n l. n < length l --> (ALL x. EL n (SNOC x l) = EL n l)"
  by (import rich_list EL_SNOC)

lemma EL_ELL: "ALL n l. n < length l --> EL n l = ELL (PRE (length l - n)) l"
  by (import rich_list EL_ELL)

lemma EL_LENGTH_APPEND: "ALL l2 l1. ~ null l2 --> EL (length l1) (l1 @ l2) = hd l2"
  by (import rich_list EL_LENGTH_APPEND)

lemma ELL_EL: "ALL n l. n < length l --> ELL n l = EL (PRE (length l - n)) l"
  by (import rich_list ELL_EL)

lemma ELL_MAP: "ALL n l f. n < length l --> ELL n (map f l) = f (ELL n l)"
  by (import rich_list ELL_MAP)

lemma LENGTH_BUTLAST: "ALL l. l ~= [] --> length (butlast l) = PRE (length l)"
  by (import rich_list LENGTH_BUTLAST)

lemma BUTFIRSTN_LENGTH_APPEND: "ALL l1 l2. BUTFIRSTN (length l1) (l1 @ l2) = l2"
  by (import rich_list BUTFIRSTN_LENGTH_APPEND)

lemma FIRSTN_APPEND1: "ALL n l1. n <= length l1 --> (ALL l2. FIRSTN n (l1 @ l2) = FIRSTN n l1)"
  by (import rich_list FIRSTN_APPEND1)

lemma FIRSTN_APPEND2: "ALL l1 n.
   length l1 <= n -->
   (ALL l2. FIRSTN n (l1 @ l2) = l1 @ FIRSTN (n - length l1) l2)"
  by (import rich_list FIRSTN_APPEND2)

lemma FIRSTN_LENGTH_APPEND: "ALL l1 l2. FIRSTN (length l1) (l1 @ l2) = l1"
  by (import rich_list FIRSTN_LENGTH_APPEND)

lemma REVERSE_FLAT: "ALL l. rev (concat l) = concat (rev (map rev l))"
  by (import rich_list REVERSE_FLAT)

lemma MAP_FILTER: "ALL f P l.
   (ALL x. P (f x) = P x) --> map f (filter P l) = filter P (map f l)"
  by (import rich_list MAP_FILTER)

lemma FLAT_REVERSE: "ALL l. concat (rev l) = rev (concat (map rev l))"
  by (import rich_list FLAT_REVERSE)

lemma FLAT_FLAT: "ALL l. concat (concat l) = concat (map concat l)"
  by (import rich_list FLAT_FLAT)

lemma ALL_EL_REVERSE: "ALL P l. list_all P (rev l) = list_all P l"
  by (import rich_list ALL_EL_REVERSE)

lemma SOME_EL_REVERSE: "ALL P l. list_exists P (rev l) = list_exists P l"
  by (import rich_list SOME_EL_REVERSE)

lemma ALL_EL_SEG: "ALL P l.
   list_all P l --> (ALL m k. m + k <= length l --> list_all P (SEG m k l))"
  by (import rich_list ALL_EL_SEG)

lemma ALL_EL_FIRSTN: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (All::('a list => bool) => bool)
      (%l::'a list.
          (op -->::bool => bool => bool)
           ((list_all::('a => bool) => 'a list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m ((size::'a list => nat) l))
                  ((list_all::('a => bool) => 'a list => bool) P
                    ((FIRSTN::nat => 'a list => 'a list) m l))))))"
  by (import rich_list ALL_EL_FIRSTN)

lemma ALL_EL_BUTFIRSTN: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (All::('a list => bool) => bool)
      (%l::'a list.
          (op -->::bool => bool => bool)
           ((list_all::('a => bool) => 'a list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m ((size::'a list => nat) l))
                  ((list_all::('a => bool) => 'a list => bool) P
                    ((BUTFIRSTN::nat => 'a list => 'a list) m l))))))"
  by (import rich_list ALL_EL_BUTFIRSTN)

lemma SOME_EL_SEG: "ALL m k l.
   m + k <= length l -->
   (ALL P. list_exists P (SEG m k l) --> list_exists P l)"
  by (import rich_list SOME_EL_SEG)

lemma SOME_EL_FIRSTN: "ALL m l.
   m <= length l --> (ALL P. list_exists P (FIRSTN m l) --> list_exists P l)"
  by (import rich_list SOME_EL_FIRSTN)

lemma SOME_EL_BUTFIRSTN: "ALL m l.
   m <= length l -->
   (ALL P. list_exists P (BUTFIRSTN m l) --> list_exists P l)"
  by (import rich_list SOME_EL_BUTFIRSTN)

lemma SOME_EL_LASTN: "ALL m l.
   m <= length l --> (ALL P. list_exists P (LASTN m l) --> list_exists P l)"
  by (import rich_list SOME_EL_LASTN)

lemma SOME_EL_BUTLASTN: "ALL m l.
   m <= length l -->
   (ALL P. list_exists P (BUTLASTN m l) --> list_exists P l)"
  by (import rich_list SOME_EL_BUTLASTN)

lemma IS_EL_REVERSE: "ALL x l. x mem rev l = x mem l"
  by (import rich_list IS_EL_REVERSE)

lemma IS_EL_FILTER: "ALL P x. P x --> (ALL l. x mem filter P l = x mem l)"
  by (import rich_list IS_EL_FILTER)

lemma IS_EL_SEG: "ALL n m l. n + m <= length l --> (ALL x. x mem SEG n m l --> x mem l)"
  by (import rich_list IS_EL_SEG)

lemma IS_EL_SOME_EL: "ALL x l. x mem l = list_exists (op = x) l"
  by (import rich_list IS_EL_SOME_EL)

lemma IS_EL_FIRSTN: "ALL x xa. x <= length xa --> (ALL xb. xb mem FIRSTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_FIRSTN)

lemma IS_EL_BUTFIRSTN: "ALL x xa. x <= length xa --> (ALL xb. xb mem BUTFIRSTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_BUTFIRSTN)

lemma IS_EL_BUTLASTN: "ALL x xa. x <= length xa --> (ALL xb. xb mem BUTLASTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_BUTLASTN)

lemma IS_EL_LASTN: "ALL x xa. x <= length xa --> (ALL xb. xb mem LASTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_LASTN)

lemma ZIP_SNOC: "ALL l1 l2.
   length l1 = length l2 -->
   (ALL x1 x2. zip (SNOC x1 l1) (SNOC x2 l2) = SNOC (x1, x2) (zip l1 l2))"
  by (import rich_list ZIP_SNOC)

lemma UNZIP_SNOC: "ALL x l.
   unzip (SNOC x l) =
   (SNOC (fst x) (fst (unzip l)), SNOC (snd x) (snd (unzip l)))"
  by (import rich_list UNZIP_SNOC)

lemma LENGTH_UNZIP_FST: "ALL x. length (UNZIP_FST x) = length x"
  by (import rich_list LENGTH_UNZIP_FST)

lemma LENGTH_UNZIP_SND: "ALL x. length (UNZIP_SND x) = length x"
  by (import rich_list LENGTH_UNZIP_SND)

lemma SUM_APPEND: "ALL l1 l2. sum (l1 @ l2) = sum l1 + sum l2"
  by (import rich_list SUM_APPEND)

lemma SUM_REVERSE: "ALL l. sum (rev l) = sum l"
  by (import rich_list SUM_REVERSE)

lemma SUM_FLAT: "ALL l. sum (concat l) = sum (map sum l)"
  by (import rich_list SUM_FLAT)

lemma EL_APPEND1: "ALL n l1 l2. n < length l1 --> EL n (l1 @ l2) = EL n l1"
  by (import rich_list EL_APPEND1)

lemma EL_APPEND2: "ALL l1 n.
   length l1 <= n --> (ALL l2. EL n (l1 @ l2) = EL (n - length l1) l2)"
  by (import rich_list EL_APPEND2)

lemma EL_MAP: "ALL n l. n < length l --> (ALL f. EL n (map f l) = f (EL n l))"
  by (import rich_list EL_MAP)

lemma EL_CONS: "ALL n. 0 < n --> (ALL x l. EL n (x # l) = EL (PRE n) l)"
  by (import rich_list EL_CONS)

lemma EL_SEG: "ALL n l. n < length l --> EL n l = hd (SEG 1 n l)"
  by (import rich_list EL_SEG)

lemma EL_IS_EL: "ALL n l. n < length l --> EL n l mem l"
  by (import rich_list EL_IS_EL)

lemma TL_SNOC: "ALL x l. tl (SNOC x l) = (if null l then [] else SNOC x (tl l))"
  by (import rich_list TL_SNOC)

lemma EL_REVERSE: "ALL n l. n < length l --> EL n (rev l) = EL (PRE (length l - n)) l"
  by (import rich_list EL_REVERSE)

lemma EL_REVERSE_ELL: "ALL n l. n < length l --> EL n (rev l) = ELL n l"
  by (import rich_list EL_REVERSE_ELL)

lemma ELL_LENGTH_APPEND: "ALL l1 l2. ~ null l1 --> ELL (length l2) (l1 @ l2) = last l1"
  by (import rich_list ELL_LENGTH_APPEND)

lemma ELL_IS_EL: "ALL n l. n < length l --> ELL n l mem l"
  by (import rich_list ELL_IS_EL)

lemma ELL_REVERSE: "ALL n l. n < length l --> ELL n (rev l) = ELL (PRE (length l - n)) l"
  by (import rich_list ELL_REVERSE)

lemma ELL_REVERSE_EL: "ALL n l. n < length l --> ELL n (rev l) = EL n l"
  by (import rich_list ELL_REVERSE_EL)

lemma FIRSTN_BUTLASTN: "ALL n l. n <= length l --> FIRSTN n l = BUTLASTN (length l - n) l"
  by (import rich_list FIRSTN_BUTLASTN)

lemma BUTLASTN_FIRSTN: "ALL n l. n <= length l --> BUTLASTN n l = FIRSTN (length l - n) l"
  by (import rich_list BUTLASTN_FIRSTN)

lemma LASTN_BUTFIRSTN: "ALL n l. n <= length l --> LASTN n l = BUTFIRSTN (length l - n) l"
  by (import rich_list LASTN_BUTFIRSTN)

lemma BUTFIRSTN_LASTN: "ALL n l. n <= length l --> BUTFIRSTN n l = LASTN (length l - n) l"
  by (import rich_list BUTFIRSTN_LASTN)

lemma SEG_LASTN_BUTLASTN: "ALL n m l.
   n + m <= length l -->
   SEG n m l = LASTN n (BUTLASTN (length l - (n + m)) l)"
  by (import rich_list SEG_LASTN_BUTLASTN)

lemma BUTFIRSTN_REVERSE: "ALL n l. n <= length l --> BUTFIRSTN n (rev l) = rev (BUTLASTN n l)"
  by (import rich_list BUTFIRSTN_REVERSE)

lemma BUTLASTN_REVERSE: "ALL n l. n <= length l --> BUTLASTN n (rev l) = rev (BUTFIRSTN n l)"
  by (import rich_list BUTLASTN_REVERSE)

lemma LASTN_REVERSE: "ALL n l. n <= length l --> LASTN n (rev l) = rev (FIRSTN n l)"
  by (import rich_list LASTN_REVERSE)

lemma FIRSTN_REVERSE: "ALL n l. n <= length l --> FIRSTN n (rev l) = rev (LASTN n l)"
  by (import rich_list FIRSTN_REVERSE)

lemma SEG_REVERSE: "ALL n m l.
   n + m <= length l -->
   SEG n m (rev l) = rev (SEG n (length l - (n + m)) l)"
  by (import rich_list SEG_REVERSE)

lemma LENGTH_GENLIST: "ALL f n. length (GENLIST f n) = n"
  by (import rich_list LENGTH_GENLIST)

lemma LENGTH_REPLICATE: "ALL n x. length (REPLICATE n x) = n"
  by (import rich_list LENGTH_REPLICATE)

lemma IS_EL_REPLICATE: "ALL n. 0 < n --> (ALL x. x mem REPLICATE n x)"
  by (import rich_list IS_EL_REPLICATE)

lemma ALL_EL_REPLICATE: "ALL x n. list_all (op = x) (REPLICATE n x)"
  by (import rich_list ALL_EL_REPLICATE)

lemma AND_EL_FOLDL: "ALL l. AND_EL l = foldl op & True l"
  by (import rich_list AND_EL_FOLDL)

lemma AND_EL_FOLDR: "ALL l. AND_EL l = foldr op & l True"
  by (import rich_list AND_EL_FOLDR)

lemma OR_EL_FOLDL: "ALL l. OR_EL l = foldl op | False l"
  by (import rich_list OR_EL_FOLDL)

lemma OR_EL_FOLDR: "ALL l. OR_EL l = foldr op | l False"
  by (import rich_list OR_EL_FOLDR)

;end_setup

;setup_theory state_transformer

constdefs
  UNIT :: "'b => 'a => 'b * 'a" 
  "(op ==::('b => 'a => 'b * 'a) => ('b => 'a => 'b * 'a) => prop)
 (UNIT::'b => 'a => 'b * 'a) (Pair::'b => 'a => 'b * 'a)"

lemma UNIT_DEF: "ALL x::'b. UNIT x = Pair x"
  by (import state_transformer UNIT_DEF)

constdefs
  BIND :: "('a => 'b * 'a) => ('b => 'a => 'c * 'a) => 'a => 'c * 'a" 
  "BIND == %g f. split f o g"

lemma BIND_DEF: "ALL g f. BIND g f = split f o g"
  by (import state_transformer BIND_DEF)

constdefs
  MMAP :: "('c => 'b) => ('a => 'c * 'a) => 'a => 'b * 'a" 
  "MMAP == %(f::'c => 'b) m::'a => 'c * 'a. BIND m (UNIT o f)"

lemma MMAP_DEF: "ALL (f::'c => 'b) m::'a => 'c * 'a. MMAP f m = BIND m (UNIT o f)"
  by (import state_transformer MMAP_DEF)

constdefs
  JOIN :: "('a => ('a => 'b * 'a) * 'a) => 'a => 'b * 'a" 
  "JOIN == %z. BIND z I"

lemma JOIN_DEF: "ALL z. JOIN z = BIND z I"
  by (import state_transformer JOIN_DEF)

lemma BIND_LEFT_UNIT: "ALL k x. BIND (UNIT x) k = k x"
  by (import state_transformer BIND_LEFT_UNIT)

lemma UNIT_UNCURRY: "ALL x. split UNIT x = x"
  by (import state_transformer UNIT_UNCURRY)

lemma BIND_RIGHT_UNIT: "ALL k. BIND k UNIT = k"
  by (import state_transformer BIND_RIGHT_UNIT)

lemma BIND_ASSOC: "ALL x xa xb. BIND x (%a. BIND (xa a) xb) = BIND (BIND x xa) xb"
  by (import state_transformer BIND_ASSOC)

lemma MMAP_ID: "MMAP I = I"
  by (import state_transformer MMAP_ID)

lemma MMAP_COMP: "ALL (f::'c => 'd) g::'b => 'c. MMAP (f o g) = MMAP f o MMAP g"
  by (import state_transformer MMAP_COMP)

lemma MMAP_UNIT: "ALL f::'b => 'c. MMAP f o UNIT = UNIT o f"
  by (import state_transformer MMAP_UNIT)

lemma MMAP_JOIN: "ALL f::'b => 'c. MMAP f o JOIN = JOIN o MMAP (MMAP f)"
  by (import state_transformer MMAP_JOIN)

lemma JOIN_UNIT: "JOIN o UNIT = I"
  by (import state_transformer JOIN_UNIT)

lemma JOIN_MMAP_UNIT: "JOIN o MMAP UNIT = I"
  by (import state_transformer JOIN_MMAP_UNIT)

lemma JOIN_MAP_JOIN: "JOIN o MMAP JOIN = JOIN o JOIN"
  by (import state_transformer JOIN_MAP_JOIN)

lemma JOIN_MAP: "ALL x xa. BIND x xa = JOIN (MMAP xa x)"
  by (import state_transformer JOIN_MAP)

lemma FST_o_UNIT: "ALL x. fst o UNIT x = K x"
  by (import state_transformer FST_o_UNIT)

lemma SND_o_UNIT: "ALL x. snd o UNIT x = I"
  by (import state_transformer SND_o_UNIT)

lemma FST_o_MMAP: "ALL x xa. fst o MMAP x xa = x o (fst o xa)"
  by (import state_transformer FST_o_MMAP)

;end_setup

end

