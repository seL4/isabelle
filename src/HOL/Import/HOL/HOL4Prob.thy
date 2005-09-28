(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Prob imports HOL4Real begin

;setup_theory prob_extra

lemma BOOL_BOOL_CASES_THM: "ALL f::bool => bool.
   f = (%b::bool. False) |
   f = (%b::bool. True) | f = (%b::bool. b) | f = Not"
  by (import prob_extra BOOL_BOOL_CASES_THM)

lemma EVEN_ODD_BASIC: "EVEN 0 & ~ EVEN 1 & EVEN 2 & ~ ODD 0 & ODD 1 & ~ ODD 2"
  by (import prob_extra EVEN_ODD_BASIC)

lemma EVEN_ODD_EXISTS_EQ: "ALL n::nat.
   EVEN n = (EX m::nat. n = 2 * m) & ODD n = (EX m::nat. n = Suc (2 * m))"
  by (import prob_extra EVEN_ODD_EXISTS_EQ)

lemma DIV_THEN_MULT: "ALL (p::nat) q::nat. Suc q * (p div Suc q) <= p"
  by (import prob_extra DIV_THEN_MULT)

lemma DIV_TWO_UNIQUE: "ALL (n::nat) (q::nat) r::nat.
   n = 2 * q + r & (r = 0 | r = 1) --> q = n div 2 & r = n mod 2"
  by (import prob_extra DIV_TWO_UNIQUE)

lemma DIVISION_TWO: "ALL n::nat. n = 2 * (n div 2) + n mod 2 & (n mod 2 = 0 | n mod 2 = 1)"
  by (import prob_extra DIVISION_TWO)

lemma DIV_TWO: "ALL n::nat. n = 2 * (n div 2) + n mod 2"
  by (import prob_extra DIV_TWO)

lemma MOD_TWO: "ALL n::nat. n mod 2 = (if EVEN n then 0 else 1)"
  by (import prob_extra MOD_TWO)

lemma DIV_TWO_BASIC: "(op &::bool => bool => bool)
 ((op =::nat => nat => bool)
   ((op div::nat => nat => nat) (0::nat)
     ((number_of::bin => nat)
       ((op BIT::bin => bit => bin)
         ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
         (bit.B0::bit))))
   (0::nat))
 ((op &::bool => bool => bool)
   ((op =::nat => nat => bool)
     ((op div::nat => nat => nat) (1::nat)
       ((number_of::bin => nat)
         ((op BIT::bin => bit => bin)
           ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
           (bit.B0::bit))))
     (0::nat))
   ((op =::nat => nat => bool)
     ((op div::nat => nat => nat)
       ((number_of::bin => nat)
         ((op BIT::bin => bit => bin)
           ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
           (bit.B0::bit)))
       ((number_of::bin => nat)
         ((op BIT::bin => bit => bin)
           ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
           (bit.B0::bit))))
     (1::nat)))"
  by (import prob_extra DIV_TWO_BASIC)

lemma DIV_TWO_MONO: "ALL (m::nat) n::nat. m div 2 < n div 2 --> m < n"
  by (import prob_extra DIV_TWO_MONO)

lemma DIV_TWO_MONO_EVEN: "ALL (m::nat) n::nat. EVEN n --> (m div 2 < n div 2) = (m < n)"
  by (import prob_extra DIV_TWO_MONO_EVEN)

lemma DIV_TWO_CANCEL: "ALL n::nat. 2 * n div 2 = n & Suc (2 * n) div 2 = n"
  by (import prob_extra DIV_TWO_CANCEL)

lemma EXP_DIV_TWO: "(All::(nat => bool) => bool)
 (%n::nat.
     (op =::nat => nat => bool)
      ((op div::nat => nat => nat)
        ((op ^::nat => nat => nat)
          ((number_of::bin => nat)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit)))
          ((Suc::nat => nat) n))
        ((number_of::bin => nat)
          ((op BIT::bin => bit => bin)
            ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
            (bit.B0::bit))))
      ((op ^::nat => nat => nat)
        ((number_of::bin => nat)
          ((op BIT::bin => bit => bin)
            ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
            (bit.B0::bit)))
        n))"
  by (import prob_extra EXP_DIV_TWO)

lemma EVEN_EXP_TWO: "ALL n::nat. EVEN (2 ^ n) = (n ~= 0)"
  by (import prob_extra EVEN_EXP_TWO)

lemma DIV_TWO_EXP: "ALL (n::nat) k::nat. (k div 2 < 2 ^ n) = (k < 2 ^ Suc n)"
  by (import prob_extra DIV_TWO_EXP)

consts
  inf :: "(real => bool) => real" 

defs
  inf_primdef: "inf == %P::real => bool. - sup (IMAGE uminus P)"

lemma inf_def: "ALL P::real => bool. inf P = - sup (IMAGE uminus P)"
  by (import prob_extra inf_def)

lemma INF_DEF_ALT: "ALL P::real => bool. inf P = - sup (%r::real. P (- r))"
  by (import prob_extra INF_DEF_ALT)

lemma REAL_SUP_EXISTS_UNIQUE: "ALL P::real => bool.
   Ex P & (EX z::real. ALL x::real. P x --> x <= z) -->
   (EX! s::real. ALL y::real. (EX x::real. P x & y < x) = (y < s))"
  by (import prob_extra REAL_SUP_EXISTS_UNIQUE)

lemma REAL_SUP_MAX: "ALL (P::real => bool) z::real.
   P z & (ALL x::real. P x --> x <= z) --> sup P = z"
  by (import prob_extra REAL_SUP_MAX)

lemma REAL_INF_MIN: "ALL (P::real => bool) z::real.
   P z & (ALL x::real. P x --> z <= x) --> inf P = z"
  by (import prob_extra REAL_INF_MIN)

lemma HALF_POS: "(op <::real => real => bool) (0::real)
 ((op /::real => real => real) (1::real)
   ((number_of::bin => real)
     ((op BIT::bin => bit => bin)
       ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
       (bit.B0::bit))))"
  by (import prob_extra HALF_POS)

lemma HALF_CANCEL: "(op =::real => real => bool)
 ((op *::real => real => real)
   ((number_of::bin => real)
     ((op BIT::bin => bit => bin)
       ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
       (bit.B0::bit)))
   ((op /::real => real => real) (1::real)
     ((number_of::bin => real)
       ((op BIT::bin => bit => bin)
         ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
         (bit.B0::bit)))))
 (1::real)"
  by (import prob_extra HALF_CANCEL)

lemma POW_HALF_POS: "(All::(nat => bool) => bool)
 (%n::nat.
     (op <::real => real => bool) (0::real)
      ((op ^::real => nat => real)
        ((op /::real => real => real) (1::real)
          ((number_of::bin => real)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit))))
        n))"
  by (import prob_extra POW_HALF_POS)

lemma POW_HALF_MONO: "(All::(nat => bool) => bool)
 (%m::nat.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool) ((op <=::nat => nat => bool) m n)
           ((op <=::real => real => bool)
             ((op ^::real => nat => real)
               ((op /::real => real => real) (1::real)
                 ((number_of::bin => real)
                   ((op BIT::bin => bit => bin)
                     ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                       (bit.B1::bit))
                     (bit.B0::bit))))
               n)
             ((op ^::real => nat => real)
               ((op /::real => real => real) (1::real)
                 ((number_of::bin => real)
                   ((op BIT::bin => bit => bin)
                     ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                       (bit.B1::bit))
                     (bit.B0::bit))))
               m))))"
  by (import prob_extra POW_HALF_MONO)

lemma POW_HALF_TWICE: "(All::(nat => bool) => bool)
 (%n::nat.
     (op =::real => real => bool)
      ((op ^::real => nat => real)
        ((op /::real => real => real) (1::real)
          ((number_of::bin => real)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit))))
        n)
      ((op *::real => real => real)
        ((number_of::bin => real)
          ((op BIT::bin => bit => bin)
            ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
            (bit.B0::bit)))
        ((op ^::real => nat => real)
          ((op /::real => real => real) (1::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))
          ((Suc::nat => nat) n))))"
  by (import prob_extra POW_HALF_TWICE)

lemma X_HALF_HALF: "ALL x::real. 1 / 2 * x + 1 / 2 * x = x"
  by (import prob_extra X_HALF_HALF)

lemma REAL_SUP_LE_X: "ALL (P::real => bool) x::real.
   Ex P & (ALL r::real. P r --> r <= x) --> sup P <= x"
  by (import prob_extra REAL_SUP_LE_X)

lemma REAL_X_LE_SUP: "ALL (P::real => bool) x::real.
   Ex P &
   (EX z::real. ALL r::real. P r --> r <= z) &
   (EX r::real. P r & x <= r) -->
   x <= sup P"
  by (import prob_extra REAL_X_LE_SUP)

lemma ABS_BETWEEN_LE: "ALL (x::real) (y::real) d::real.
   (0 <= d & x - d <= y & y <= x + d) = (abs (y - x) <= d)"
  by (import prob_extra ABS_BETWEEN_LE)

lemma ONE_MINUS_HALF: "(op =::real => real => bool)
 ((op -::real => real => real) (1::real)
   ((op /::real => real => real) (1::real)
     ((number_of::bin => real)
       ((op BIT::bin => bit => bin)
         ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
         (bit.B0::bit)))))
 ((op /::real => real => real) (1::real)
   ((number_of::bin => real)
     ((op BIT::bin => bit => bin)
       ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
       (bit.B0::bit))))"
  by (import prob_extra ONE_MINUS_HALF)

lemma HALF_LT_1: "(op <::real => real => bool)
 ((op /::real => real => real) (1::real)
   ((number_of::bin => real)
     ((op BIT::bin => bit => bin)
       ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
       (bit.B0::bit))))
 (1::real)"
  by (import prob_extra HALF_LT_1)

lemma POW_HALF_EXP: "(All::(nat => bool) => bool)
 (%n::nat.
     (op =::real => real => bool)
      ((op ^::real => nat => real)
        ((op /::real => real => real) (1::real)
          ((number_of::bin => real)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit))))
        n)
      ((inverse::real => real)
        ((real::nat => real)
          ((op ^::nat => nat => nat)
            ((number_of::bin => nat)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))
            n))))"
  by (import prob_extra POW_HALF_EXP)

lemma INV_SUC_POS: "ALL n::nat. 0 < 1 / real (Suc n)"
  by (import prob_extra INV_SUC_POS)

lemma INV_SUC_MAX: "ALL x::nat. 1 / real (Suc x) <= 1"
  by (import prob_extra INV_SUC_MAX)

lemma INV_SUC: "ALL n::nat. 0 < 1 / real (Suc n) & 1 / real (Suc n) <= 1"
  by (import prob_extra INV_SUC)

lemma ABS_UNIT_INTERVAL: "ALL (x::real) y::real.
   0 <= x & x <= 1 & 0 <= y & y <= 1 --> abs (x - y) <= 1"
  by (import prob_extra ABS_UNIT_INTERVAL)

lemma MEM_NIL: "ALL l::'a::type list. (ALL x::'a::type. ~ x mem l) = (l = [])"
  by (import prob_extra MEM_NIL)

lemma MAP_MEM: "ALL (f::'a::type => 'b::type) (l::'a::type list) x::'b::type.
   x mem map f l = (EX y::'a::type. y mem l & x = f y)"
  by (import prob_extra MAP_MEM)

lemma MEM_NIL_MAP_CONS: "ALL (x::'a::type) l::'a::type list list. ~ [] mem map (op # x) l"
  by (import prob_extra MEM_NIL_MAP_CONS)

lemma FILTER_TRUE: "ALL l::'a::type list. [x::'a::type:l. True] = l"
  by (import prob_extra FILTER_TRUE)

lemma FILTER_FALSE: "ALL l::'a::type list. [x::'a::type:l. False] = []"
  by (import prob_extra FILTER_FALSE)

lemma FILTER_MEM: "ALL (P::'a::type => bool) (x::'a::type) l::'a::type list.
   x mem filter P l --> P x"
  by (import prob_extra FILTER_MEM)

lemma MEM_FILTER: "ALL (P::'a::type => bool) (l::'a::type list) x::'a::type.
   x mem filter P l --> x mem l"
  by (import prob_extra MEM_FILTER)

lemma FILTER_OUT_ELT: "ALL (x::'a::type) l::'a::type list. x mem l | [y::'a::type:l. y ~= x] = l"
  by (import prob_extra FILTER_OUT_ELT)

lemma IS_PREFIX_NIL: "ALL x::'a::type list. IS_PREFIX x [] & IS_PREFIX [] x = (x = [])"
  by (import prob_extra IS_PREFIX_NIL)

lemma IS_PREFIX_REFL: "ALL x::'a::type list. IS_PREFIX x x"
  by (import prob_extra IS_PREFIX_REFL)

lemma IS_PREFIX_ANTISYM: "ALL (x::'a::type list) y::'a::type list.
   IS_PREFIX y x & IS_PREFIX x y --> x = y"
  by (import prob_extra IS_PREFIX_ANTISYM)

lemma IS_PREFIX_TRANS: "ALL (x::'a::type list) (y::'a::type list) z::'a::type list.
   IS_PREFIX x y & IS_PREFIX y z --> IS_PREFIX x z"
  by (import prob_extra IS_PREFIX_TRANS)

lemma IS_PREFIX_BUTLAST: "ALL (x::'a::type) y::'a::type list. IS_PREFIX (x # y) (butlast (x # y))"
  by (import prob_extra IS_PREFIX_BUTLAST)

lemma IS_PREFIX_LENGTH: "ALL (x::'a::type list) y::'a::type list.
   IS_PREFIX y x --> length x <= length y"
  by (import prob_extra IS_PREFIX_LENGTH)

lemma IS_PREFIX_LENGTH_ANTI: "ALL (x::'a::type list) y::'a::type list.
   IS_PREFIX y x & length x = length y --> x = y"
  by (import prob_extra IS_PREFIX_LENGTH_ANTI)

lemma IS_PREFIX_SNOC: "ALL (x::'a::type) (y::'a::type list) z::'a::type list.
   IS_PREFIX (SNOC x y) z = (IS_PREFIX y z | z = SNOC x y)"
  by (import prob_extra IS_PREFIX_SNOC)

lemma FOLDR_MAP: "ALL (f::'b::type => 'c::type => 'c::type) (e::'c::type)
   (g::'a::type => 'b::type) l::'a::type list.
   foldr f (map g l) e = foldr (%x::'a::type. f (g x)) l e"
  by (import prob_extra FOLDR_MAP)

lemma LAST_MEM: "ALL (h::'a::type) t::'a::type list. last (h # t) mem h # t"
  by (import prob_extra LAST_MEM)

lemma LAST_MAP_CONS: "ALL (b::bool) (h::bool list) t::bool list list.
   EX x::bool list. last (map (op # b) (h # t)) = b # x"
  by (import prob_extra LAST_MAP_CONS)

lemma EXISTS_LONGEST: "ALL (x::'a::type list) y::'a::type list list.
   EX z::'a::type list.
      z mem x # y &
      (ALL w::'a::type list. w mem x # y --> length w <= length z)"
  by (import prob_extra EXISTS_LONGEST)

lemma UNION_DEF_ALT: "ALL (s::'a::type => bool) t::'a::type => bool.
   pred_set.UNION s t = (%x::'a::type. s x | t x)"
  by (import prob_extra UNION_DEF_ALT)

lemma INTER_UNION_RDISTRIB: "ALL (p::'a::type => bool) (q::'a::type => bool) r::'a::type => bool.
   pred_set.INTER (pred_set.UNION p q) r =
   pred_set.UNION (pred_set.INTER p r) (pred_set.INTER q r)"
  by (import prob_extra INTER_UNION_RDISTRIB)

lemma SUBSET_EQ: "ALL (x::'a::type => bool) xa::'a::type => bool.
   (x = xa) = (SUBSET x xa & SUBSET xa x)"
  by (import prob_extra SUBSET_EQ)

lemma INTER_IS_EMPTY: "ALL (s::'a::type => bool) t::'a::type => bool.
   (pred_set.INTER s t = EMPTY) = (ALL x::'a::type. ~ s x | ~ t x)"
  by (import prob_extra INTER_IS_EMPTY)

lemma UNION_DISJOINT_SPLIT: "ALL (s::'a::type => bool) (t::'a::type => bool) u::'a::type => bool.
   pred_set.UNION s t = pred_set.UNION s u &
   pred_set.INTER s t = EMPTY & pred_set.INTER s u = EMPTY -->
   t = u"
  by (import prob_extra UNION_DISJOINT_SPLIT)

lemma GSPEC_DEF_ALT: "ALL f::'a::type => 'b::type * bool.
   GSPEC f = (%v::'b::type. EX x::'a::type. (v, True) = f x)"
  by (import prob_extra GSPEC_DEF_ALT)

;end_setup

;setup_theory prob_canon

consts
  alg_twin :: "bool list => bool list => bool" 

defs
  alg_twin_primdef: "alg_twin ==
%(x::bool list) y::bool list.
   EX l::bool list. x = SNOC True l & y = SNOC False l"

lemma alg_twin_def: "ALL (x::bool list) y::bool list.
   alg_twin x y = (EX l::bool list. x = SNOC True l & y = SNOC False l)"
  by (import prob_canon alg_twin_def)

constdefs
  alg_order_tupled :: "bool list * bool list => bool" 
  "(op ==::(bool list * bool list => bool)
        => (bool list * bool list => bool) => prop)
 (alg_order_tupled::bool list * bool list => bool)
 ((WFREC::(bool list * bool list => bool list * bool list => bool)
          => ((bool list * bool list => bool)
              => bool list * bool list => bool)
             => bool list * bool list => bool)
   ((Eps::((bool list * bool list => bool list * bool list => bool) => bool)
          => bool list * bool list => bool list * bool list => bool)
     (%R::bool list * bool list => bool list * bool list => bool.
         (op &::bool => bool => bool)
          ((WF::(bool list * bool list => bool list * bool list => bool)
                => bool)
            R)
          ((All::(bool => bool) => bool)
            (%h'::bool.
                (All::(bool => bool) => bool)
                 (%h::bool.
                     (All::(bool list => bool) => bool)
                      (%t'::bool list.
                          (All::(bool list => bool) => bool)
                           (%t::bool list.
                               R ((Pair::bool list
   => bool list => bool list * bool list)
                                   t t')
                                ((Pair::bool list
  => bool list => bool list * bool list)
                                  ((op #::bool => bool list => bool list) h
                                    t)
                                  ((op #::bool => bool list => bool list) h'
                                    t')))))))))
   (%alg_order_tupled::bool list * bool list => bool.
       (split::(bool list => bool list => bool)
               => bool list * bool list => bool)
        (%(v::bool list) v1::bool list.
            (list_case::bool
                        => (bool => bool list => bool) => bool list => bool)
             ((list_case::bool
                          => (bool => bool list => bool)
                             => bool list => bool)
               (True::bool) (%(v8::bool) v9::bool list. True::bool) v1)
             (%(v4::bool) v5::bool list.
                 (list_case::bool
                             => (bool => bool list => bool)
                                => bool list => bool)
                  (False::bool)
                  (%(v10::bool) v11::bool list.
                      (op |::bool => bool => bool)
                       ((op &::bool => bool => bool)
                         ((op =::bool => bool => bool) v4 (True::bool))
                         ((op =::bool => bool => bool) v10 (False::bool)))
                       ((op &::bool => bool => bool)
                         ((op =::bool => bool => bool) v4 v10)
                         (alg_order_tupled
                           ((Pair::bool list
                                   => bool list => bool list * bool list)
                             v5 v11))))
                  v1)
             v)))"

lemma alg_order_tupled_primitive_def: "(op =::(bool list * bool list => bool)
       => (bool list * bool list => bool) => bool)
 (alg_order_tupled::bool list * bool list => bool)
 ((WFREC::(bool list * bool list => bool list * bool list => bool)
          => ((bool list * bool list => bool)
              => bool list * bool list => bool)
             => bool list * bool list => bool)
   ((Eps::((bool list * bool list => bool list * bool list => bool) => bool)
          => bool list * bool list => bool list * bool list => bool)
     (%R::bool list * bool list => bool list * bool list => bool.
         (op &::bool => bool => bool)
          ((WF::(bool list * bool list => bool list * bool list => bool)
                => bool)
            R)
          ((All::(bool => bool) => bool)
            (%h'::bool.
                (All::(bool => bool) => bool)
                 (%h::bool.
                     (All::(bool list => bool) => bool)
                      (%t'::bool list.
                          (All::(bool list => bool) => bool)
                           (%t::bool list.
                               R ((Pair::bool list
   => bool list => bool list * bool list)
                                   t t')
                                ((Pair::bool list
  => bool list => bool list * bool list)
                                  ((op #::bool => bool list => bool list) h
                                    t)
                                  ((op #::bool => bool list => bool list) h'
                                    t')))))))))
   (%alg_order_tupled::bool list * bool list => bool.
       (split::(bool list => bool list => bool)
               => bool list * bool list => bool)
        (%(v::bool list) v1::bool list.
            (list_case::bool
                        => (bool => bool list => bool) => bool list => bool)
             ((list_case::bool
                          => (bool => bool list => bool)
                             => bool list => bool)
               (True::bool) (%(v8::bool) v9::bool list. True::bool) v1)
             (%(v4::bool) v5::bool list.
                 (list_case::bool
                             => (bool => bool list => bool)
                                => bool list => bool)
                  (False::bool)
                  (%(v10::bool) v11::bool list.
                      (op |::bool => bool => bool)
                       ((op &::bool => bool => bool)
                         ((op =::bool => bool => bool) v4 (True::bool))
                         ((op =::bool => bool => bool) v10 (False::bool)))
                       ((op &::bool => bool => bool)
                         ((op =::bool => bool => bool) v4 v10)
                         (alg_order_tupled
                           ((Pair::bool list
                                   => bool list => bool list * bool list)
                             v5 v11))))
                  v1)
             v)))"
  by (import prob_canon alg_order_tupled_primitive_def)

consts
  alg_order :: "bool list => bool list => bool" 

defs
  alg_order_primdef: "alg_order == %(x::bool list) x1::bool list. alg_order_tupled (x, x1)"

lemma alg_order_curried_def: "ALL (x::bool list) x1::bool list. alg_order x x1 = alg_order_tupled (x, x1)"
  by (import prob_canon alg_order_curried_def)

lemma alg_order_ind: "ALL P::bool list => bool list => bool.
   (ALL (x::bool) xa::bool list. P [] (x # xa)) &
   P [] [] &
   (ALL (x::bool) xa::bool list. P (x # xa) []) &
   (ALL (x::bool) (xa::bool list) (xb::bool) xc::bool list.
       P xa xc --> P (x # xa) (xb # xc)) -->
   (ALL x::bool list. All (P x))"
  by (import prob_canon alg_order_ind)

lemma alg_order_def: "alg_order [] ((v6::bool) # (v7::bool list)) = True &
alg_order [] [] = True &
alg_order ((v2::bool) # (v3::bool list)) [] = False &
alg_order ((h::bool) # (t::bool list)) ((h'::bool) # (t'::bool list)) =
(h = True & h' = False | h = h' & alg_order t t')"
  by (import prob_canon alg_order_def)

consts
  alg_sorted :: "bool list list => bool" 

defs
  alg_sorted_primdef: "alg_sorted ==
WFREC
 (SOME R::bool list list => bool list list => bool.
     WF R &
     (ALL (x::bool list) (z::bool list list) y::bool list.
         R (y # z) (x # y # z)))
 (%alg_sorted::bool list list => bool.
     list_case True
      (%v2::bool list.
          list_case True
           (%(v6::bool list) v7::bool list list.
               alg_order v2 v6 & alg_sorted (v6 # v7))))"

lemma alg_sorted_primitive_def: "alg_sorted =
WFREC
 (SOME R::bool list list => bool list list => bool.
     WF R &
     (ALL (x::bool list) (z::bool list list) y::bool list.
         R (y # z) (x # y # z)))
 (%alg_sorted::bool list list => bool.
     list_case True
      (%v2::bool list.
          list_case True
           (%(v6::bool list) v7::bool list list.
               alg_order v2 v6 & alg_sorted (v6 # v7))))"
  by (import prob_canon alg_sorted_primitive_def)

lemma alg_sorted_ind: "ALL P::bool list list => bool.
   (ALL (x::bool list) (y::bool list) z::bool list list.
       P (y # z) --> P (x # y # z)) &
   (ALL v::bool list. P [v]) & P [] -->
   All P"
  by (import prob_canon alg_sorted_ind)

lemma alg_sorted_def: "alg_sorted ((x::bool list) # (y::bool list) # (z::bool list list)) =
(alg_order x y & alg_sorted (y # z)) &
alg_sorted [v::bool list] = True & alg_sorted [] = True"
  by (import prob_canon alg_sorted_def)

consts
  alg_prefixfree :: "bool list list => bool" 

defs
  alg_prefixfree_primdef: "alg_prefixfree ==
WFREC
 (SOME R::bool list list => bool list list => bool.
     WF R &
     (ALL (x::bool list) (z::bool list list) y::bool list.
         R (y # z) (x # y # z)))
 (%alg_prefixfree::bool list list => bool.
     list_case True
      (%v2::bool list.
          list_case True
           (%(v6::bool list) v7::bool list list.
               ~ IS_PREFIX v6 v2 & alg_prefixfree (v6 # v7))))"

lemma alg_prefixfree_primitive_def: "alg_prefixfree =
WFREC
 (SOME R::bool list list => bool list list => bool.
     WF R &
     (ALL (x::bool list) (z::bool list list) y::bool list.
         R (y # z) (x # y # z)))
 (%alg_prefixfree::bool list list => bool.
     list_case True
      (%v2::bool list.
          list_case True
           (%(v6::bool list) v7::bool list list.
               ~ IS_PREFIX v6 v2 & alg_prefixfree (v6 # v7))))"
  by (import prob_canon alg_prefixfree_primitive_def)

lemma alg_prefixfree_ind: "ALL P::bool list list => bool.
   (ALL (x::bool list) (y::bool list) z::bool list list.
       P (y # z) --> P (x # y # z)) &
   (ALL v::bool list. P [v]) & P [] -->
   All P"
  by (import prob_canon alg_prefixfree_ind)

lemma alg_prefixfree_def: "alg_prefixfree ((x::bool list) # (y::bool list) # (z::bool list list)) =
(~ IS_PREFIX y x & alg_prefixfree (y # z)) &
alg_prefixfree [v::bool list] = True & alg_prefixfree [] = True"
  by (import prob_canon alg_prefixfree_def)

consts
  alg_twinfree :: "bool list list => bool" 

defs
  alg_twinfree_primdef: "alg_twinfree ==
WFREC
 (SOME R::bool list list => bool list list => bool.
     WF R &
     (ALL (x::bool list) (z::bool list list) y::bool list.
         R (y # z) (x # y # z)))
 (%alg_twinfree::bool list list => bool.
     list_case True
      (%v2::bool list.
          list_case True
           (%(v6::bool list) v7::bool list list.
               ~ alg_twin v2 v6 & alg_twinfree (v6 # v7))))"

lemma alg_twinfree_primitive_def: "alg_twinfree =
WFREC
 (SOME R::bool list list => bool list list => bool.
     WF R &
     (ALL (x::bool list) (z::bool list list) y::bool list.
         R (y # z) (x # y # z)))
 (%alg_twinfree::bool list list => bool.
     list_case True
      (%v2::bool list.
          list_case True
           (%(v6::bool list) v7::bool list list.
               ~ alg_twin v2 v6 & alg_twinfree (v6 # v7))))"
  by (import prob_canon alg_twinfree_primitive_def)

lemma alg_twinfree_ind: "ALL P::bool list list => bool.
   (ALL (x::bool list) (y::bool list) z::bool list list.
       P (y # z) --> P (x # y # z)) &
   (ALL v::bool list. P [v]) & P [] -->
   All P"
  by (import prob_canon alg_twinfree_ind)

lemma alg_twinfree_def: "alg_twinfree ((x::bool list) # (y::bool list) # (z::bool list list)) =
(~ alg_twin x y & alg_twinfree (y # z)) &
alg_twinfree [v::bool list] = True & alg_twinfree [] = True"
  by (import prob_canon alg_twinfree_def)

consts
  alg_longest :: "bool list list => nat" 

defs
  alg_longest_primdef: "alg_longest ==
FOLDR (%(h::bool list) t::nat. if t <= length h then length h else t) 0"

lemma alg_longest_def: "alg_longest =
FOLDR (%(h::bool list) t::nat. if t <= length h then length h else t) 0"
  by (import prob_canon alg_longest_def)

consts
  alg_canon_prefs :: "bool list => bool list list => bool list list" 

specification (alg_canon_prefs_primdef: alg_canon_prefs) alg_canon_prefs_def: "(ALL l::bool list. alg_canon_prefs l [] = [l]) &
(ALL (l::bool list) (h::bool list) t::bool list list.
    alg_canon_prefs l (h # t) =
    (if IS_PREFIX h l then alg_canon_prefs l t else l # h # t))"
  by (import prob_canon alg_canon_prefs_def)

consts
  alg_canon_find :: "bool list => bool list list => bool list list" 

specification (alg_canon_find_primdef: alg_canon_find) alg_canon_find_def: "(ALL l::bool list. alg_canon_find l [] = [l]) &
(ALL (l::bool list) (h::bool list) t::bool list list.
    alg_canon_find l (h # t) =
    (if alg_order h l
     then if IS_PREFIX l h then h # t else h # alg_canon_find l t
     else alg_canon_prefs l (h # t)))"
  by (import prob_canon alg_canon_find_def)

consts
  alg_canon1 :: "bool list list => bool list list" 

defs
  alg_canon1_primdef: "alg_canon1 == FOLDR alg_canon_find []"

lemma alg_canon1_def: "alg_canon1 = FOLDR alg_canon_find []"
  by (import prob_canon alg_canon1_def)

consts
  alg_canon_merge :: "bool list => bool list list => bool list list" 

specification (alg_canon_merge_primdef: alg_canon_merge) alg_canon_merge_def: "(ALL l::bool list. alg_canon_merge l [] = [l]) &
(ALL (l::bool list) (h::bool list) t::bool list list.
    alg_canon_merge l (h # t) =
    (if alg_twin l h then alg_canon_merge (butlast h) t else l # h # t))"
  by (import prob_canon alg_canon_merge_def)

consts
  alg_canon2 :: "bool list list => bool list list" 

defs
  alg_canon2_primdef: "alg_canon2 == FOLDR alg_canon_merge []"

lemma alg_canon2_def: "alg_canon2 = FOLDR alg_canon_merge []"
  by (import prob_canon alg_canon2_def)

consts
  alg_canon :: "bool list list => bool list list" 

defs
  alg_canon_primdef: "alg_canon == %l::bool list list. alg_canon2 (alg_canon1 l)"

lemma alg_canon_def: "ALL l::bool list list. alg_canon l = alg_canon2 (alg_canon1 l)"
  by (import prob_canon alg_canon_def)

consts
  algebra_canon :: "bool list list => bool" 

defs
  algebra_canon_primdef: "algebra_canon == %l::bool list list. alg_canon l = l"

lemma algebra_canon_def: "ALL l::bool list list. algebra_canon l = (alg_canon l = l)"
  by (import prob_canon algebra_canon_def)

lemma ALG_TWIN_NIL: "ALL l::bool list. ~ alg_twin l [] & ~ alg_twin [] l"
  by (import prob_canon ALG_TWIN_NIL)

lemma ALG_TWIN_SING: "ALL (x::bool) l::bool list.
   alg_twin [x] l = (x = True & l = [False]) &
   alg_twin l [x] = (l = [True] & x = False)"
  by (import prob_canon ALG_TWIN_SING)

lemma ALG_TWIN_CONS: "ALL (x::bool) (y::bool) (z::bool list) (h::bool) t::bool list.
   alg_twin (x # y # z) (h # t) = (x = h & alg_twin (y # z) t) &
   alg_twin (h # t) (x # y # z) = (x = h & alg_twin t (y # z))"
  by (import prob_canon ALG_TWIN_CONS)

lemma ALG_TWIN_REDUCE: "ALL (h::bool) (t::bool list) t'::bool list.
   alg_twin (h # t) (h # t') = alg_twin t t'"
  by (import prob_canon ALG_TWIN_REDUCE)

lemma ALG_TWINS_PREFIX: "ALL (x::bool list) l::bool list.
   IS_PREFIX x l -->
   x = l | IS_PREFIX x (SNOC True l) | IS_PREFIX x (SNOC False l)"
  by (import prob_canon ALG_TWINS_PREFIX)

lemma ALG_ORDER_NIL: "ALL x::bool list. alg_order [] x & alg_order x [] = (x = [])"
  by (import prob_canon ALG_ORDER_NIL)

lemma ALG_ORDER_REFL: "ALL x::bool list. alg_order x x"
  by (import prob_canon ALG_ORDER_REFL)

lemma ALG_ORDER_ANTISYM: "ALL (x::bool list) y::bool list. alg_order x y & alg_order y x --> x = y"
  by (import prob_canon ALG_ORDER_ANTISYM)

lemma ALG_ORDER_TRANS: "ALL (x::bool list) (y::bool list) z::bool list.
   alg_order x y & alg_order y z --> alg_order x z"
  by (import prob_canon ALG_ORDER_TRANS)

lemma ALG_ORDER_TOTAL: "ALL (x::bool list) y::bool list. alg_order x y | alg_order y x"
  by (import prob_canon ALG_ORDER_TOTAL)

lemma ALG_ORDER_PREFIX: "ALL (x::bool list) y::bool list. IS_PREFIX y x --> alg_order x y"
  by (import prob_canon ALG_ORDER_PREFIX)

lemma ALG_ORDER_PREFIX_ANTI: "ALL (x::bool list) y::bool list. alg_order x y & IS_PREFIX x y --> x = y"
  by (import prob_canon ALG_ORDER_PREFIX_ANTI)

lemma ALG_ORDER_PREFIX_MONO: "ALL (x::bool list) (y::bool list) z::bool list.
   alg_order x y & alg_order y z & IS_PREFIX z x --> IS_PREFIX y x"
  by (import prob_canon ALG_ORDER_PREFIX_MONO)

lemma ALG_ORDER_PREFIX_TRANS: "ALL (x::bool list) (y::bool list) z::bool list.
   alg_order x y & IS_PREFIX y z --> alg_order x z | IS_PREFIX x z"
  by (import prob_canon ALG_ORDER_PREFIX_TRANS)

lemma ALG_ORDER_SNOC: "ALL (x::bool) l::bool list. ~ alg_order (SNOC x l) l"
  by (import prob_canon ALG_ORDER_SNOC)

lemma ALG_SORTED_MIN: "ALL (h::bool list) t::bool list list.
   alg_sorted (h # t) --> (ALL x::bool list. x mem t --> alg_order h x)"
  by (import prob_canon ALG_SORTED_MIN)

lemma ALG_SORTED_DEF_ALT: "ALL (h::bool list) t::bool list list.
   alg_sorted (h # t) =
   ((ALL x::bool list. x mem t --> alg_order h x) & alg_sorted t)"
  by (import prob_canon ALG_SORTED_DEF_ALT)

lemma ALG_SORTED_TL: "ALL (h::bool list) t::bool list list. alg_sorted (h # t) --> alg_sorted t"
  by (import prob_canon ALG_SORTED_TL)

lemma ALG_SORTED_MONO: "ALL (x::bool list) (y::bool list) z::bool list list.
   alg_sorted (x # y # z) --> alg_sorted (x # z)"
  by (import prob_canon ALG_SORTED_MONO)

lemma ALG_SORTED_TLS: "ALL (l::bool list list) b::bool. alg_sorted (map (op # b) l) = alg_sorted l"
  by (import prob_canon ALG_SORTED_TLS)

lemma ALG_SORTED_STEP: "ALL (l1::bool list list) l2::bool list list.
   alg_sorted (map (op # True) l1 @ map (op # False) l2) =
   (alg_sorted l1 & alg_sorted l2)"
  by (import prob_canon ALG_SORTED_STEP)

lemma ALG_SORTED_APPEND: "ALL (h::bool list) (h'::bool list) (t::bool list list) t'::bool list list.
   alg_sorted ((h # t) @ h' # t') =
   (alg_sorted (h # t) & alg_sorted (h' # t') & alg_order (last (h # t)) h')"
  by (import prob_canon ALG_SORTED_APPEND)

lemma ALG_SORTED_FILTER: "ALL (P::bool list => bool) b::bool list list.
   alg_sorted b --> alg_sorted (filter P b)"
  by (import prob_canon ALG_SORTED_FILTER)

lemma ALG_PREFIXFREE_TL: "ALL (h::bool list) t::bool list list.
   alg_prefixfree (h # t) --> alg_prefixfree t"
  by (import prob_canon ALG_PREFIXFREE_TL)

lemma ALG_PREFIXFREE_MONO: "ALL (x::bool list) (y::bool list) z::bool list list.
   alg_sorted (x # y # z) & alg_prefixfree (x # y # z) -->
   alg_prefixfree (x # z)"
  by (import prob_canon ALG_PREFIXFREE_MONO)

lemma ALG_PREFIXFREE_ELT: "ALL (h::bool list) t::bool list list.
   alg_sorted (h # t) & alg_prefixfree (h # t) -->
   (ALL x::bool list. x mem t --> ~ IS_PREFIX x h & ~ IS_PREFIX h x)"
  by (import prob_canon ALG_PREFIXFREE_ELT)

lemma ALG_PREFIXFREE_TLS: "ALL (l::bool list list) b::bool.
   alg_prefixfree (map (op # b) l) = alg_prefixfree l"
  by (import prob_canon ALG_PREFIXFREE_TLS)

lemma ALG_PREFIXFREE_STEP: "ALL (l1::bool list list) l2::bool list list.
   alg_prefixfree (map (op # True) l1 @ map (op # False) l2) =
   (alg_prefixfree l1 & alg_prefixfree l2)"
  by (import prob_canon ALG_PREFIXFREE_STEP)

lemma ALG_PREFIXFREE_APPEND: "ALL (h::bool list) (h'::bool list) (t::bool list list) t'::bool list list.
   alg_prefixfree ((h # t) @ h' # t') =
   (alg_prefixfree (h # t) &
    alg_prefixfree (h' # t') & ~ IS_PREFIX h' (last (h # t)))"
  by (import prob_canon ALG_PREFIXFREE_APPEND)

lemma ALG_PREFIXFREE_FILTER: "ALL (P::bool list => bool) b::bool list list.
   alg_sorted b & alg_prefixfree b --> alg_prefixfree (filter P b)"
  by (import prob_canon ALG_PREFIXFREE_FILTER)

lemma ALG_TWINFREE_TL: "ALL (h::bool list) t::bool list list.
   alg_twinfree (h # t) --> alg_twinfree t"
  by (import prob_canon ALG_TWINFREE_TL)

lemma ALG_TWINFREE_TLS: "ALL (l::bool list list) b::bool.
   alg_twinfree (map (op # b) l) = alg_twinfree l"
  by (import prob_canon ALG_TWINFREE_TLS)

lemma ALG_TWINFREE_STEP1: "ALL (l1::bool list list) l2::bool list list.
   alg_twinfree (map (op # True) l1 @ map (op # False) l2) -->
   alg_twinfree l1 & alg_twinfree l2"
  by (import prob_canon ALG_TWINFREE_STEP1)

lemma ALG_TWINFREE_STEP2: "ALL (l1::bool list list) l2::bool list list.
   (~ [] mem l1 | ~ [] mem l2) & alg_twinfree l1 & alg_twinfree l2 -->
   alg_twinfree (map (op # True) l1 @ map (op # False) l2)"
  by (import prob_canon ALG_TWINFREE_STEP2)

lemma ALG_TWINFREE_STEP: "ALL (l1::bool list list) l2::bool list list.
   ~ [] mem l1 | ~ [] mem l2 -->
   alg_twinfree (map (op # True) l1 @ map (op # False) l2) =
   (alg_twinfree l1 & alg_twinfree l2)"
  by (import prob_canon ALG_TWINFREE_STEP)

lemma ALG_LONGEST_HD: "ALL (h::bool list) t::bool list list. length h <= alg_longest (h # t)"
  by (import prob_canon ALG_LONGEST_HD)

lemma ALG_LONGEST_TL: "ALL (h::bool list) t::bool list list. alg_longest t <= alg_longest (h # t)"
  by (import prob_canon ALG_LONGEST_TL)

lemma ALG_LONGEST_TLS: "ALL (h::bool list) (t::bool list list) b::bool.
   alg_longest (map (op # b) (h # t)) = Suc (alg_longest (h # t))"
  by (import prob_canon ALG_LONGEST_TLS)

lemma ALG_LONGEST_APPEND: "ALL (l1::bool list list) l2::bool list list.
   alg_longest l1 <= alg_longest (l1 @ l2) &
   alg_longest l2 <= alg_longest (l1 @ l2)"
  by (import prob_canon ALG_LONGEST_APPEND)

lemma ALG_CANON_PREFS_HD: "ALL (l::bool list) b::bool list list. hd (alg_canon_prefs l b) = l"
  by (import prob_canon ALG_CANON_PREFS_HD)

lemma ALG_CANON_PREFS_DELETES: "ALL (l::bool list) (b::bool list list) x::bool list.
   x mem alg_canon_prefs l b --> x mem l # b"
  by (import prob_canon ALG_CANON_PREFS_DELETES)

lemma ALG_CANON_PREFS_SORTED: "ALL (l::bool list) b::bool list list.
   alg_sorted (l # b) --> alg_sorted (alg_canon_prefs l b)"
  by (import prob_canon ALG_CANON_PREFS_SORTED)

lemma ALG_CANON_PREFS_PREFIXFREE: "ALL (l::bool list) b::bool list list.
   alg_sorted b & alg_prefixfree b --> alg_prefixfree (alg_canon_prefs l b)"
  by (import prob_canon ALG_CANON_PREFS_PREFIXFREE)

lemma ALG_CANON_PREFS_CONSTANT: "ALL (l::bool list) b::bool list list.
   alg_prefixfree (l # b) --> alg_canon_prefs l b = l # b"
  by (import prob_canon ALG_CANON_PREFS_CONSTANT)

lemma ALG_CANON_FIND_HD: "ALL (l::bool list) (h::bool list) t::bool list list.
   hd (alg_canon_find l (h # t)) = l | hd (alg_canon_find l (h # t)) = h"
  by (import prob_canon ALG_CANON_FIND_HD)

lemma ALG_CANON_FIND_DELETES: "ALL (l::bool list) (b::bool list list) x::bool list.
   x mem alg_canon_find l b --> x mem l # b"
  by (import prob_canon ALG_CANON_FIND_DELETES)

lemma ALG_CANON_FIND_SORTED: "ALL (l::bool list) b::bool list list.
   alg_sorted b --> alg_sorted (alg_canon_find l b)"
  by (import prob_canon ALG_CANON_FIND_SORTED)

lemma ALG_CANON_FIND_PREFIXFREE: "ALL (l::bool list) b::bool list list.
   alg_sorted b & alg_prefixfree b --> alg_prefixfree (alg_canon_find l b)"
  by (import prob_canon ALG_CANON_FIND_PREFIXFREE)

lemma ALG_CANON_FIND_CONSTANT: "ALL (l::bool list) b::bool list list.
   alg_sorted (l # b) & alg_prefixfree (l # b) -->
   alg_canon_find l b = l # b"
  by (import prob_canon ALG_CANON_FIND_CONSTANT)

lemma ALG_CANON1_SORTED: "ALL x::bool list list. alg_sorted (alg_canon1 x)"
  by (import prob_canon ALG_CANON1_SORTED)

lemma ALG_CANON1_PREFIXFREE: "ALL l::bool list list. alg_prefixfree (alg_canon1 l)"
  by (import prob_canon ALG_CANON1_PREFIXFREE)

lemma ALG_CANON1_CONSTANT: "ALL l::bool list list. alg_sorted l & alg_prefixfree l --> alg_canon1 l = l"
  by (import prob_canon ALG_CANON1_CONSTANT)

lemma ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE: "ALL (l::bool list) b::bool list list.
   alg_sorted (l # b) & alg_prefixfree (l # b) & alg_twinfree b -->
   alg_sorted (alg_canon_merge l b) &
   alg_prefixfree (alg_canon_merge l b) & alg_twinfree (alg_canon_merge l b)"
  by (import prob_canon ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON_MERGE_PREFIXFREE_PRESERVE: "ALL (l::bool list) (b::bool list list) h::bool list.
   (ALL x::bool list. x mem l # b --> ~ IS_PREFIX h x & ~ IS_PREFIX x h) -->
   (ALL x::bool list.
       x mem alg_canon_merge l b --> ~ IS_PREFIX h x & ~ IS_PREFIX x h)"
  by (import prob_canon ALG_CANON_MERGE_PREFIXFREE_PRESERVE)

lemma ALG_CANON_MERGE_SHORTENS: "ALL (l::bool list) (b::bool list list) x::bool list.
   x mem alg_canon_merge l b -->
   (EX y::bool list. y mem l # b & IS_PREFIX y x)"
  by (import prob_canon ALG_CANON_MERGE_SHORTENS)

lemma ALG_CANON_MERGE_CONSTANT: "ALL (l::bool list) b::bool list list.
   alg_twinfree (l # b) --> alg_canon_merge l b = l # b"
  by (import prob_canon ALG_CANON_MERGE_CONSTANT)

lemma ALG_CANON2_PREFIXFREE_PRESERVE: "ALL (x::bool list list) xa::bool list.
   (ALL xb::bool list.
       xb mem x --> ~ IS_PREFIX xa xb & ~ IS_PREFIX xb xa) -->
   (ALL xb::bool list.
       xb mem alg_canon2 x --> ~ IS_PREFIX xa xb & ~ IS_PREFIX xb xa)"
  by (import prob_canon ALG_CANON2_PREFIXFREE_PRESERVE)

lemma ALG_CANON2_SHORTENS: "ALL (x::bool list list) xa::bool list.
   xa mem alg_canon2 x --> (EX y::bool list. y mem x & IS_PREFIX y xa)"
  by (import prob_canon ALG_CANON2_SHORTENS)

lemma ALG_CANON2_SORTED_PREFIXFREE_TWINFREE: "ALL x::bool list list.
   alg_sorted x & alg_prefixfree x -->
   alg_sorted (alg_canon2 x) &
   alg_prefixfree (alg_canon2 x) & alg_twinfree (alg_canon2 x)"
  by (import prob_canon ALG_CANON2_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON2_CONSTANT: "ALL l::bool list list. alg_twinfree l --> alg_canon2 l = l"
  by (import prob_canon ALG_CANON2_CONSTANT)

lemma ALG_CANON_SORTED_PREFIXFREE_TWINFREE: "ALL l::bool list list.
   alg_sorted (alg_canon l) &
   alg_prefixfree (alg_canon l) & alg_twinfree (alg_canon l)"
  by (import prob_canon ALG_CANON_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON_CONSTANT: "ALL l::bool list list.
   alg_sorted l & alg_prefixfree l & alg_twinfree l --> alg_canon l = l"
  by (import prob_canon ALG_CANON_CONSTANT)

lemma ALG_CANON_IDEMPOT: "ALL l::bool list list. alg_canon (alg_canon l) = alg_canon l"
  by (import prob_canon ALG_CANON_IDEMPOT)

lemma ALGEBRA_CANON_DEF_ALT: "ALL l::bool list list.
   algebra_canon l = (alg_sorted l & alg_prefixfree l & alg_twinfree l)"
  by (import prob_canon ALGEBRA_CANON_DEF_ALT)

lemma ALGEBRA_CANON_BASIC: "algebra_canon [] &
algebra_canon [[]] & (ALL x::bool list. algebra_canon [x])"
  by (import prob_canon ALGEBRA_CANON_BASIC)

lemma ALG_CANON_BASIC: "alg_canon [] = [] &
alg_canon [[]] = [[]] & (ALL x::bool list. alg_canon [x] = [x])"
  by (import prob_canon ALG_CANON_BASIC)

lemma ALGEBRA_CANON_TL: "ALL (h::bool list) t::bool list list.
   algebra_canon (h # t) --> algebra_canon t"
  by (import prob_canon ALGEBRA_CANON_TL)

lemma ALGEBRA_CANON_NIL_MEM: "ALL l::bool list list. (algebra_canon l & [] mem l) = (l = [[]])"
  by (import prob_canon ALGEBRA_CANON_NIL_MEM)

lemma ALGEBRA_CANON_TLS: "ALL (l::bool list list) b::bool.
   algebra_canon (map (op # b) l) = algebra_canon l"
  by (import prob_canon ALGEBRA_CANON_TLS)

lemma ALGEBRA_CANON_STEP1: "ALL (l1::bool list list) l2::bool list list.
   algebra_canon (map (op # True) l1 @ map (op # False) l2) -->
   algebra_canon l1 & algebra_canon l2"
  by (import prob_canon ALGEBRA_CANON_STEP1)

lemma ALGEBRA_CANON_STEP2: "ALL (l1::bool list list) l2::bool list list.
   (l1 ~= [[]] | l2 ~= [[]]) & algebra_canon l1 & algebra_canon l2 -->
   algebra_canon (map (op # True) l1 @ map (op # False) l2)"
  by (import prob_canon ALGEBRA_CANON_STEP2)

lemma ALGEBRA_CANON_STEP: "ALL (l1::bool list list) l2::bool list list.
   l1 ~= [[]] | l2 ~= [[]] -->
   algebra_canon (map (op # True) l1 @ map (op # False) l2) =
   (algebra_canon l1 & algebra_canon l2)"
  by (import prob_canon ALGEBRA_CANON_STEP)

lemma ALGEBRA_CANON_CASES_THM: "ALL l::bool list list.
   algebra_canon l -->
   l = [] |
   l = [[]] |
   (EX (l1::bool list list) l2::bool list list.
       algebra_canon l1 &
       algebra_canon l2 & l = map (op # True) l1 @ map (op # False) l2)"
  by (import prob_canon ALGEBRA_CANON_CASES_THM)

lemma ALGEBRA_CANON_CASES: "ALL P::bool list list => bool.
   P [] &
   P [[]] &
   (ALL (l1::bool list list) l2::bool list list.
       algebra_canon l1 &
       algebra_canon l2 &
       algebra_canon (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2)) -->
   (ALL l::bool list list. algebra_canon l --> P l)"
  by (import prob_canon ALGEBRA_CANON_CASES)

lemma ALGEBRA_CANON_INDUCTION: "ALL P::bool list list => bool.
   P [] &
   P [[]] &
   (ALL (l1::bool list list) l2::bool list list.
       algebra_canon l1 &
       algebra_canon l2 &
       P l1 &
       P l2 & algebra_canon (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2)) -->
   (ALL l::bool list list. algebra_canon l --> P l)"
  by (import prob_canon ALGEBRA_CANON_INDUCTION)

lemma MEM_NIL_STEP: "ALL (l1::bool list list) l2::bool list list.
   ~ [] mem map (op # True) l1 @ map (op # False) l2"
  by (import prob_canon MEM_NIL_STEP)

lemma ALG_SORTED_PREFIXFREE_MEM_NIL: "ALL l::bool list list.
   (alg_sorted l & alg_prefixfree l & [] mem l) = (l = [[]])"
  by (import prob_canon ALG_SORTED_PREFIXFREE_MEM_NIL)

lemma ALG_SORTED_PREFIXFREE_EQUALITY: "ALL (l::bool list list) l'::bool list list.
   (ALL x::bool list. x mem l = x mem l') &
   alg_sorted l & alg_sorted l' & alg_prefixfree l & alg_prefixfree l' -->
   l = l'"
  by (import prob_canon ALG_SORTED_PREFIXFREE_EQUALITY)

;end_setup

;setup_theory boolean_sequence

consts
  SHD :: "(nat => bool) => bool" 

defs
  SHD_primdef: "SHD == %f::nat => bool. f 0"

lemma SHD_def: "ALL f::nat => bool. SHD f = f 0"
  by (import boolean_sequence SHD_def)

consts
  STL :: "(nat => bool) => nat => bool" 

defs
  STL_primdef: "STL == %(f::nat => bool) n::nat. f (Suc n)"

lemma STL_def: "ALL (f::nat => bool) n::nat. STL f n = f (Suc n)"
  by (import boolean_sequence STL_def)

consts
  SCONS :: "bool => (nat => bool) => nat => bool" 

specification (SCONS_primdef: SCONS) SCONS_def: "(ALL (h::bool) t::nat => bool. SCONS h t 0 = h) &
(ALL (h::bool) (t::nat => bool) n::nat. SCONS h t (Suc n) = t n)"
  by (import boolean_sequence SCONS_def)

consts
  SDEST :: "(nat => bool) => bool * (nat => bool)" 

defs
  SDEST_primdef: "SDEST == %s::nat => bool. (SHD s, STL s)"

lemma SDEST_def: "SDEST = (%s::nat => bool. (SHD s, STL s))"
  by (import boolean_sequence SDEST_def)

consts
  SCONST :: "bool => nat => bool" 

defs
  SCONST_primdef: "SCONST == K"

lemma SCONST_def: "SCONST = K"
  by (import boolean_sequence SCONST_def)

consts
  STAKE :: "nat => (nat => bool) => bool list" 

specification (STAKE_primdef: STAKE) STAKE_def: "(ALL s::nat => bool. STAKE 0 s = []) &
(ALL (n::nat) s::nat => bool. STAKE (Suc n) s = SHD s # STAKE n (STL s))"
  by (import boolean_sequence STAKE_def)

consts
  SDROP :: "nat => (nat => bool) => nat => bool" 

specification (SDROP_primdef: SDROP) SDROP_def: "SDROP 0 = I & (ALL n::nat. SDROP (Suc n) = SDROP n o STL)"
  by (import boolean_sequence SDROP_def)

lemma SCONS_SURJ: "ALL x::nat => bool. EX (xa::bool) t::nat => bool. x = SCONS xa t"
  by (import boolean_sequence SCONS_SURJ)

lemma SHD_STL_ISO: "ALL (h::bool) t::nat => bool. EX x::nat => bool. SHD x = h & STL x = t"
  by (import boolean_sequence SHD_STL_ISO)

lemma SHD_SCONS: "ALL (h::bool) t::nat => bool. SHD (SCONS h t) = h"
  by (import boolean_sequence SHD_SCONS)

lemma STL_SCONS: "ALL (h::bool) t::nat => bool. STL (SCONS h t) = t"
  by (import boolean_sequence STL_SCONS)

lemma SHD_SCONST: "ALL b::bool. SHD (SCONST b) = b"
  by (import boolean_sequence SHD_SCONST)

lemma STL_SCONST: "ALL b::bool. STL (SCONST b) = SCONST b"
  by (import boolean_sequence STL_SCONST)

;end_setup

;setup_theory prob_algebra

consts
  alg_embed :: "bool list => (nat => bool) => bool" 

specification (alg_embed_primdef: alg_embed) alg_embed_def: "(ALL s::nat => bool. alg_embed [] s = True) &
(ALL (h::bool) (t::bool list) s::nat => bool.
    alg_embed (h # t) s = (h = SHD s & alg_embed t (STL s)))"
  by (import prob_algebra alg_embed_def)

consts
  algebra_embed :: "bool list list => (nat => bool) => bool" 

specification (algebra_embed_primdef: algebra_embed) algebra_embed_def: "algebra_embed [] = EMPTY &
(ALL (h::bool list) t::bool list list.
    algebra_embed (h # t) = pred_set.UNION (alg_embed h) (algebra_embed t))"
  by (import prob_algebra algebra_embed_def)

consts
  measurable :: "((nat => bool) => bool) => bool" 

defs
  measurable_primdef: "measurable ==
%s::(nat => bool) => bool. EX b::bool list list. s = algebra_embed b"

lemma measurable_def: "ALL s::(nat => bool) => bool.
   measurable s = (EX b::bool list list. s = algebra_embed b)"
  by (import prob_algebra measurable_def)

lemma HALVES_INTER: "pred_set.INTER (%x::nat => bool. SHD x = True)
 (%x::nat => bool. SHD x = False) =
EMPTY"
  by (import prob_algebra HALVES_INTER)

lemma INTER_STL: "ALL (p::(nat => bool) => bool) q::(nat => bool) => bool.
   pred_set.INTER p q o STL = pred_set.INTER (p o STL) (q o STL)"
  by (import prob_algebra INTER_STL)

lemma COMPL_SHD: "ALL b::bool.
   COMPL (%x::nat => bool. SHD x = b) = (%x::nat => bool. SHD x = (~ b))"
  by (import prob_algebra COMPL_SHD)

lemma ALG_EMBED_BASIC: "alg_embed [] = pred_set.UNIV &
(ALL (h::bool) t::bool list.
    alg_embed (h # t) =
    pred_set.INTER (%x::nat => bool. SHD x = h) (alg_embed t o STL))"
  by (import prob_algebra ALG_EMBED_BASIC)

lemma ALG_EMBED_NIL: "ALL c::bool list. All (alg_embed c) = (c = [])"
  by (import prob_algebra ALG_EMBED_NIL)

lemma ALG_EMBED_POPULATED: "ALL b::bool list. Ex (alg_embed b)"
  by (import prob_algebra ALG_EMBED_POPULATED)

lemma ALG_EMBED_PREFIX: "ALL (b::bool list) (c::bool list) s::nat => bool.
   alg_embed b s & alg_embed c s --> IS_PREFIX b c | IS_PREFIX c b"
  by (import prob_algebra ALG_EMBED_PREFIX)

lemma ALG_EMBED_PREFIX_SUBSET: "ALL (b::bool list) c::bool list.
   SUBSET (alg_embed b) (alg_embed c) = IS_PREFIX b c"
  by (import prob_algebra ALG_EMBED_PREFIX_SUBSET)

lemma ALG_EMBED_TWINS: "ALL l::bool list.
   pred_set.UNION (alg_embed (SNOC True l)) (alg_embed (SNOC False l)) =
   alg_embed l"
  by (import prob_algebra ALG_EMBED_TWINS)

lemma ALGEBRA_EMBED_BASIC: "algebra_embed [] = EMPTY &
algebra_embed [[]] = pred_set.UNIV &
(ALL b::bool. algebra_embed [[b]] = (%s::nat => bool. SHD s = b))"
  by (import prob_algebra ALGEBRA_EMBED_BASIC)

lemma ALGEBRA_EMBED_MEM: "ALL (b::bool list list) x::nat => bool.
   algebra_embed b x --> (EX l::bool list. l mem b & alg_embed l x)"
  by (import prob_algebra ALGEBRA_EMBED_MEM)

lemma ALGEBRA_EMBED_APPEND: "ALL (l1::bool list list) l2::bool list list.
   algebra_embed (l1 @ l2) =
   pred_set.UNION (algebra_embed l1) (algebra_embed l2)"
  by (import prob_algebra ALGEBRA_EMBED_APPEND)

lemma ALGEBRA_EMBED_TLS: "ALL (l::bool list list) b::bool.
   algebra_embed (map (op # b) l) (SCONS (h::bool) (t::nat => bool)) =
   (h = b & algebra_embed l t)"
  by (import prob_algebra ALGEBRA_EMBED_TLS)

lemma ALG_CANON_PREFS_EMBED: "ALL (l::bool list) b::bool list list.
   algebra_embed (alg_canon_prefs l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_PREFS_EMBED)

lemma ALG_CANON_FIND_EMBED: "ALL (l::bool list) b::bool list list.
   algebra_embed (alg_canon_find l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_FIND_EMBED)

lemma ALG_CANON1_EMBED: "ALL x::bool list list. algebra_embed (alg_canon1 x) = algebra_embed x"
  by (import prob_algebra ALG_CANON1_EMBED)

lemma ALG_CANON_MERGE_EMBED: "ALL (l::bool list) b::bool list list.
   algebra_embed (alg_canon_merge l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_MERGE_EMBED)

lemma ALG_CANON2_EMBED: "ALL x::bool list list. algebra_embed (alg_canon2 x) = algebra_embed x"
  by (import prob_algebra ALG_CANON2_EMBED)

lemma ALG_CANON_EMBED: "ALL l::bool list list. algebra_embed (alg_canon l) = algebra_embed l"
  by (import prob_algebra ALG_CANON_EMBED)

lemma ALGEBRA_CANON_UNIV: "ALL l::bool list list.
   algebra_canon l --> algebra_embed l = pred_set.UNIV --> l = [[]]"
  by (import prob_algebra ALGEBRA_CANON_UNIV)

lemma ALG_CANON_REP: "ALL (b::bool list list) c::bool list list.
   (alg_canon b = alg_canon c) = (algebra_embed b = algebra_embed c)"
  by (import prob_algebra ALG_CANON_REP)

lemma ALGEBRA_CANON_EMBED_EMPTY: "ALL l::bool list list.
   algebra_canon l --> (ALL v::nat => bool. ~ algebra_embed l v) = (l = [])"
  by (import prob_algebra ALGEBRA_CANON_EMBED_EMPTY)

lemma ALGEBRA_CANON_EMBED_UNIV: "ALL l::bool list list.
   algebra_canon l --> All (algebra_embed l) = (l = [[]])"
  by (import prob_algebra ALGEBRA_CANON_EMBED_UNIV)

lemma MEASURABLE_ALGEBRA: "ALL b::bool list list. measurable (algebra_embed b)"
  by (import prob_algebra MEASURABLE_ALGEBRA)

lemma MEASURABLE_BASIC: "measurable EMPTY &
measurable pred_set.UNIV &
(ALL b::bool. measurable (%s::nat => bool. SHD s = b))"
  by (import prob_algebra MEASURABLE_BASIC)

lemma MEASURABLE_SHD: "ALL b::bool. measurable (%s::nat => bool. SHD s = b)"
  by (import prob_algebra MEASURABLE_SHD)

lemma ALGEBRA_EMBED_COMPL: "ALL l::bool list list.
   EX l'::bool list list. COMPL (algebra_embed l) = algebra_embed l'"
  by (import prob_algebra ALGEBRA_EMBED_COMPL)

lemma MEASURABLE_COMPL: "ALL s::(nat => bool) => bool. measurable (COMPL s) = measurable s"
  by (import prob_algebra MEASURABLE_COMPL)

lemma MEASURABLE_UNION: "ALL (s::(nat => bool) => bool) t::(nat => bool) => bool.
   measurable s & measurable t --> measurable (pred_set.UNION s t)"
  by (import prob_algebra MEASURABLE_UNION)

lemma MEASURABLE_INTER: "ALL (s::(nat => bool) => bool) t::(nat => bool) => bool.
   measurable s & measurable t --> measurable (pred_set.INTER s t)"
  by (import prob_algebra MEASURABLE_INTER)

lemma MEASURABLE_STL: "ALL p::(nat => bool) => bool. measurable (p o STL) = measurable p"
  by (import prob_algebra MEASURABLE_STL)

lemma MEASURABLE_SDROP: "ALL (n::nat) p::(nat => bool) => bool.
   measurable (p o SDROP n) = measurable p"
  by (import prob_algebra MEASURABLE_SDROP)

lemma MEASURABLE_INTER_HALVES: "ALL p::(nat => bool) => bool.
   (measurable (pred_set.INTER (%x::nat => bool. SHD x = True) p) &
    measurable (pred_set.INTER (%x::nat => bool. SHD x = False) p)) =
   measurable p"
  by (import prob_algebra MEASURABLE_INTER_HALVES)

lemma MEASURABLE_HALVES: "ALL (p::(nat => bool) => bool) q::(nat => bool) => bool.
   measurable
    (pred_set.UNION (pred_set.INTER (%x::nat => bool. SHD x = True) p)
      (pred_set.INTER (%x::nat => bool. SHD x = False) q)) =
   (measurable (pred_set.INTER (%x::nat => bool. SHD x = True) p) &
    measurable (pred_set.INTER (%x::nat => bool. SHD x = False) q))"
  by (import prob_algebra MEASURABLE_HALVES)

lemma MEASURABLE_INTER_SHD: "ALL (b::bool) p::(nat => bool) => bool.
   measurable (pred_set.INTER (%x::nat => bool. SHD x = b) (p o STL)) =
   measurable p"
  by (import prob_algebra MEASURABLE_INTER_SHD)

;end_setup

;setup_theory prob

consts
  alg_measure :: "bool list list => real" 

specification (alg_measure_primdef: alg_measure) alg_measure_def: "alg_measure [] = 0 &
(ALL (l::bool list) rest::bool list list.
    alg_measure (l # rest) = (1 / 2) ^ length l + alg_measure rest)"
  by (import prob alg_measure_def)

consts
  algebra_measure :: "bool list list => real" 

defs
  algebra_measure_primdef: "algebra_measure ==
%b::bool list list.
   inf (%r::real.
           EX c::bool list list.
              algebra_embed b = algebra_embed c & alg_measure c = r)"

lemma algebra_measure_def: "ALL b::bool list list.
   algebra_measure b =
   inf (%r::real.
           EX c::bool list list.
              algebra_embed b = algebra_embed c & alg_measure c = r)"
  by (import prob algebra_measure_def)

consts
  prob :: "((nat => bool) => bool) => real" 

defs
  prob_primdef: "prob ==
%s::(nat => bool) => bool.
   sup (%r::real.
           EX b::bool list list.
              algebra_measure b = r & SUBSET (algebra_embed b) s)"

lemma prob_def: "ALL s::(nat => bool) => bool.
   prob s =
   sup (%r::real.
           EX b::bool list list.
              algebra_measure b = r & SUBSET (algebra_embed b) s)"
  by (import prob prob_def)

lemma ALG_TWINS_MEASURE: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (op =::real => real => bool)
      ((op +::real => real => real)
        ((op ^::real => nat => real)
          ((op /::real => real => real) (1::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))
          ((size::bool list => nat)
            ((SNOC::bool => bool list => bool list) (True::bool) l)))
        ((op ^::real => nat => real)
          ((op /::real => real => real) (1::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))
          ((size::bool list => nat)
            ((SNOC::bool => bool list => bool list) (False::bool) l))))
      ((op ^::real => nat => real)
        ((op /::real => real => real) (1::real)
          ((number_of::bin => real)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit))))
        ((size::bool list => nat) l)))"
  by (import prob ALG_TWINS_MEASURE)

lemma ALG_MEASURE_BASIC: "alg_measure [] = 0 &
alg_measure [[]] = 1 & (ALL b::bool. alg_measure [[b]] = 1 / 2)"
  by (import prob ALG_MEASURE_BASIC)

lemma ALG_MEASURE_POS: "ALL l::bool list list. 0 <= alg_measure l"
  by (import prob ALG_MEASURE_POS)

lemma ALG_MEASURE_APPEND: "ALL (l1::bool list list) l2::bool list list.
   alg_measure (l1 @ l2) = alg_measure l1 + alg_measure l2"
  by (import prob ALG_MEASURE_APPEND)

lemma ALG_MEASURE_TLS: "ALL (l::bool list list) b::bool.
   2 * alg_measure (map (op # b) l) = alg_measure l"
  by (import prob ALG_MEASURE_TLS)

lemma ALG_CANON_PREFS_MONO: "ALL (l::bool list) b::bool list list.
   alg_measure (alg_canon_prefs l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_PREFS_MONO)

lemma ALG_CANON_FIND_MONO: "ALL (l::bool list) b::bool list list.
   alg_measure (alg_canon_find l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_FIND_MONO)

lemma ALG_CANON1_MONO: "ALL x::bool list list. alg_measure (alg_canon1 x) <= alg_measure x"
  by (import prob ALG_CANON1_MONO)

lemma ALG_CANON_MERGE_MONO: "ALL (l::bool list) b::bool list list.
   alg_measure (alg_canon_merge l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_MERGE_MONO)

lemma ALG_CANON2_MONO: "ALL x::bool list list. alg_measure (alg_canon2 x) <= alg_measure x"
  by (import prob ALG_CANON2_MONO)

lemma ALG_CANON_MONO: "ALL l::bool list list. alg_measure (alg_canon l) <= alg_measure l"
  by (import prob ALG_CANON_MONO)

lemma ALGEBRA_MEASURE_DEF_ALT: "ALL l::bool list list. algebra_measure l = alg_measure (alg_canon l)"
  by (import prob ALGEBRA_MEASURE_DEF_ALT)

lemma ALGEBRA_MEASURE_BASIC: "algebra_measure [] = 0 &
algebra_measure [[]] = 1 & (ALL b::bool. algebra_measure [[b]] = 1 / 2)"
  by (import prob ALGEBRA_MEASURE_BASIC)

lemma ALGEBRA_CANON_MEASURE_MAX: "ALL l::bool list list. algebra_canon l --> alg_measure l <= 1"
  by (import prob ALGEBRA_CANON_MEASURE_MAX)

lemma ALGEBRA_MEASURE_MAX: "ALL l::bool list list. algebra_measure l <= 1"
  by (import prob ALGEBRA_MEASURE_MAX)

lemma ALGEBRA_MEASURE_MONO_EMBED: "ALL (x::bool list list) xa::bool list list.
   SUBSET (algebra_embed x) (algebra_embed xa) -->
   algebra_measure x <= algebra_measure xa"
  by (import prob ALGEBRA_MEASURE_MONO_EMBED)

lemma ALG_MEASURE_COMPL: "ALL l::bool list list.
   algebra_canon l -->
   (ALL c::bool list list.
       algebra_canon c -->
       COMPL (algebra_embed l) = algebra_embed c -->
       alg_measure l + alg_measure c = 1)"
  by (import prob ALG_MEASURE_COMPL)

lemma ALG_MEASURE_ADDITIVE: "ALL l::bool list list.
   algebra_canon l -->
   (ALL c::bool list list.
       algebra_canon c -->
       (ALL d::bool list list.
           algebra_canon d -->
           pred_set.INTER (algebra_embed c) (algebra_embed d) = EMPTY &
           algebra_embed l =
           pred_set.UNION (algebra_embed c) (algebra_embed d) -->
           alg_measure l = alg_measure c + alg_measure d))"
  by (import prob ALG_MEASURE_ADDITIVE)

lemma PROB_ALGEBRA: "ALL l::bool list list. prob (algebra_embed l) = algebra_measure l"
  by (import prob PROB_ALGEBRA)

lemma PROB_BASIC: "prob EMPTY = 0 &
prob pred_set.UNIV = 1 &
(ALL b::bool. prob (%s::nat => bool. SHD s = b) = 1 / 2)"
  by (import prob PROB_BASIC)

lemma PROB_ADDITIVE: "ALL (s::(nat => bool) => bool) t::(nat => bool) => bool.
   measurable s & measurable t & pred_set.INTER s t = EMPTY -->
   prob (pred_set.UNION s t) = prob s + prob t"
  by (import prob PROB_ADDITIVE)

lemma PROB_COMPL: "ALL s::(nat => bool) => bool. measurable s --> prob (COMPL s) = 1 - prob s"
  by (import prob PROB_COMPL)

lemma PROB_SUP_EXISTS1: "ALL s::(nat => bool) => bool.
   EX (x::real) b::bool list list.
      algebra_measure b = x & SUBSET (algebra_embed b) s"
  by (import prob PROB_SUP_EXISTS1)

lemma PROB_SUP_EXISTS2: "ALL s::(nat => bool) => bool.
   EX x::real.
      ALL r::real.
         (EX b::bool list list.
             algebra_measure b = r & SUBSET (algebra_embed b) s) -->
         r <= x"
  by (import prob PROB_SUP_EXISTS2)

lemma PROB_LE_X: "ALL (s::(nat => bool) => bool) x::real.
   (ALL s'::(nat => bool) => bool.
       measurable s' & SUBSET s' s --> prob s' <= x) -->
   prob s <= x"
  by (import prob PROB_LE_X)

lemma X_LE_PROB: "ALL (s::(nat => bool) => bool) x::real.
   (EX s'::(nat => bool) => bool.
       measurable s' & SUBSET s' s & x <= prob s') -->
   x <= prob s"
  by (import prob X_LE_PROB)

lemma PROB_SUBSET_MONO: "ALL (s::(nat => bool) => bool) t::(nat => bool) => bool.
   SUBSET s t --> prob s <= prob t"
  by (import prob PROB_SUBSET_MONO)

lemma PROB_ALG: "ALL x::bool list. prob (alg_embed x) = (1 / 2) ^ length x"
  by (import prob PROB_ALG)

lemma PROB_STL: "ALL p::(nat => bool) => bool. measurable p --> prob (p o STL) = prob p"
  by (import prob PROB_STL)

lemma PROB_SDROP: "ALL (n::nat) p::(nat => bool) => bool.
   measurable p --> prob (p o SDROP n) = prob p"
  by (import prob PROB_SDROP)

lemma PROB_INTER_HALVES: "ALL p::(nat => bool) => bool.
   measurable p -->
   prob (pred_set.INTER (%x::nat => bool. SHD x = True) p) +
   prob (pred_set.INTER (%x::nat => bool. SHD x = False) p) =
   prob p"
  by (import prob PROB_INTER_HALVES)

lemma PROB_INTER_SHD: "ALL (b::bool) p::(nat => bool) => bool.
   measurable p -->
   prob (pred_set.INTER (%x::nat => bool. SHD x = b) (p o STL)) =
   1 / 2 * prob p"
  by (import prob PROB_INTER_SHD)

lemma ALGEBRA_MEASURE_POS: "ALL l::bool list list. 0 <= algebra_measure l"
  by (import prob ALGEBRA_MEASURE_POS)

lemma ALGEBRA_MEASURE_RANGE: "ALL l::bool list list. 0 <= algebra_measure l & algebra_measure l <= 1"
  by (import prob ALGEBRA_MEASURE_RANGE)

lemma PROB_POS: "ALL p::(nat => bool) => bool. 0 <= prob p"
  by (import prob PROB_POS)

lemma PROB_MAX: "ALL p::(nat => bool) => bool. prob p <= 1"
  by (import prob PROB_MAX)

lemma PROB_RANGE: "ALL p::(nat => bool) => bool. 0 <= prob p & prob p <= 1"
  by (import prob PROB_RANGE)

lemma ABS_PROB: "ALL p::(nat => bool) => bool. abs (prob p) = prob p"
  by (import prob ABS_PROB)

lemma PROB_SHD: "ALL b::bool. prob (%s::nat => bool. SHD s = b) = 1 / 2"
  by (import prob PROB_SHD)

lemma PROB_COMPL_LE1: "ALL (p::(nat => bool) => bool) r::real.
   measurable p --> (prob (COMPL p) <= r) = (1 - r <= prob p)"
  by (import prob PROB_COMPL_LE1)

;end_setup

;setup_theory prob_pseudo

consts
  pseudo_linear_hd :: "nat => bool" 

defs
  pseudo_linear_hd_primdef: "pseudo_linear_hd == EVEN"

lemma pseudo_linear_hd_def: "pseudo_linear_hd = EVEN"
  by (import prob_pseudo pseudo_linear_hd_def)

consts
  pseudo_linear_tl :: "nat => nat => nat => nat => nat" 

defs
  pseudo_linear_tl_primdef: "pseudo_linear_tl ==
%(a::nat) (b::nat) (n::nat) x::nat. (a * x + b) mod (2 * n + 1)"

lemma pseudo_linear_tl_def: "ALL (a::nat) (b::nat) (n::nat) x::nat.
   pseudo_linear_tl a b n x = (a * x + b) mod (2 * n + 1)"
  by (import prob_pseudo pseudo_linear_tl_def)

lemma PSEUDO_LINEAR1_EXECUTE: "EX x::nat => nat => bool.
   (ALL xa::nat. SHD (x xa) = pseudo_linear_hd xa) &
   (ALL xa::nat.
       STL (x xa) =
       x (pseudo_linear_tl
           (NUMERAL
             (NUMERAL_BIT1
               (NUMERAL_BIT1
                 (NUMERAL_BIT1
                   (NUMERAL_BIT2 (NUMERAL_BIT1 (NUMERAL_BIT2 ALT_ZERO)))))))
           (NUMERAL
             (NUMERAL_BIT1
               (NUMERAL_BIT1
                 (NUMERAL_BIT1
                   (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT2 ALT_ZERO)))))))
           (NUMERAL
             (NUMERAL_BIT1
               (NUMERAL_BIT1
                 (NUMERAL_BIT1
                   (NUMERAL_BIT1 (NUMERAL_BIT2 (NUMERAL_BIT1 ALT_ZERO)))))))
           xa))"
  by (import prob_pseudo PSEUDO_LINEAR1_EXECUTE)

consts
  pseudo_linear1 :: "nat => nat => bool" 

specification (pseudo_linear1_primdef: pseudo_linear1) pseudo_linear1_def: "(ALL x::nat. SHD (pseudo_linear1 x) = pseudo_linear_hd x) &
(ALL x::nat.
    STL (pseudo_linear1 x) =
    pseudo_linear1
     (pseudo_linear_tl
       (NUMERAL
         (NUMERAL_BIT1
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT2 (NUMERAL_BIT1 (NUMERAL_BIT2 ALT_ZERO)))))))
       (NUMERAL
         (NUMERAL_BIT1
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT2 ALT_ZERO)))))))
       (NUMERAL
         (NUMERAL_BIT1
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT2 (NUMERAL_BIT1 ALT_ZERO)))))))
       x))"
  by (import prob_pseudo pseudo_linear1_def)

consts
  pseudo :: "nat => nat => bool" 

defs
  pseudo_primdef: "pseudo == pseudo_linear1"

lemma pseudo_def: "pseudo = pseudo_linear1"
  by (import prob_pseudo pseudo_def)

;end_setup

;setup_theory prob_indep

consts
  indep_set :: "((nat => bool) => bool) => ((nat => bool) => bool) => bool" 

defs
  indep_set_primdef: "indep_set ==
%(p::(nat => bool) => bool) q::(nat => bool) => bool.
   measurable p & measurable q & prob (pred_set.INTER p q) = prob p * prob q"

lemma indep_set_def: "ALL (p::(nat => bool) => bool) q::(nat => bool) => bool.
   indep_set p q =
   (measurable p &
    measurable q & prob (pred_set.INTER p q) = prob p * prob q)"
  by (import prob_indep indep_set_def)

consts
  alg_cover_set :: "bool list list => bool" 

defs
  alg_cover_set_primdef: "alg_cover_set ==
%l::bool list list.
   alg_sorted l & alg_prefixfree l & algebra_embed l = pred_set.UNIV"

lemma alg_cover_set_def: "ALL l::bool list list.
   alg_cover_set l =
   (alg_sorted l & alg_prefixfree l & algebra_embed l = pred_set.UNIV)"
  by (import prob_indep alg_cover_set_def)

consts
  alg_cover :: "bool list list => (nat => bool) => bool list" 

defs
  alg_cover_primdef: "alg_cover ==
%(l::bool list list) x::nat => bool.
   SOME b::bool list. b mem l & alg_embed b x"

lemma alg_cover_def: "ALL (l::bool list list) x::nat => bool.
   alg_cover l x = (SOME b::bool list. b mem l & alg_embed b x)"
  by (import prob_indep alg_cover_def)

consts
  indep :: "((nat => bool) => 'a * (nat => bool)) => bool" 

defs
  indep_primdef: "indep ==
%f::(nat => bool) => 'a::type * (nat => bool).
   EX (l::bool list list) r::bool list => 'a::type.
      alg_cover_set l &
      (ALL s::nat => bool.
          f s =
          (let c::bool list = alg_cover l s in (r c, SDROP (length c) s)))"

lemma indep_def: "ALL f::(nat => bool) => 'a::type * (nat => bool).
   indep f =
   (EX (l::bool list list) r::bool list => 'a::type.
       alg_cover_set l &
       (ALL s::nat => bool.
           f s =
           (let c::bool list = alg_cover l s in (r c, SDROP (length c) s))))"
  by (import prob_indep indep_def)

lemma INDEP_SET_BASIC: "ALL p::(nat => bool) => bool.
   measurable p --> indep_set EMPTY p & indep_set pred_set.UNIV p"
  by (import prob_indep INDEP_SET_BASIC)

lemma INDEP_SET_SYM: "ALL (p::(nat => bool) => bool) q::(nat => bool) => bool.
   indep_set p q = indep_set p q"
  by (import prob_indep INDEP_SET_SYM)

lemma INDEP_SET_DISJOINT_DECOMP: "ALL (p::(nat => bool) => bool) (q::(nat => bool) => bool)
   r::(nat => bool) => bool.
   indep_set p r & indep_set q r & pred_set.INTER p q = EMPTY -->
   indep_set (pred_set.UNION p q) r"
  by (import prob_indep INDEP_SET_DISJOINT_DECOMP)

lemma ALG_COVER_SET_BASIC: "~ alg_cover_set [] & alg_cover_set [[]] & alg_cover_set [[True], [False]]"
  by (import prob_indep ALG_COVER_SET_BASIC)

lemma ALG_COVER_WELL_DEFINED: "ALL (l::bool list list) x::nat => bool.
   alg_cover_set l --> alg_cover l x mem l & alg_embed (alg_cover l x) x"
  by (import prob_indep ALG_COVER_WELL_DEFINED)

lemma ALG_COVER_UNIV: "alg_cover [[]] = K []"
  by (import prob_indep ALG_COVER_UNIV)

lemma MAP_CONS_TL_FILTER: "ALL (l::bool list list) b::bool.
   ~ [] mem l -->
   map (op # b) (map tl [x::bool list:l. hd x = b]) =
   [x::bool list:l. hd x = b]"
  by (import prob_indep MAP_CONS_TL_FILTER)

lemma ALG_COVER_SET_CASES_THM: "ALL l::bool list list.
   alg_cover_set l =
   (l = [[]] |
    (EX (x::bool list list) xa::bool list list.
        alg_cover_set x &
        alg_cover_set xa & l = map (op # True) x @ map (op # False) xa))"
  by (import prob_indep ALG_COVER_SET_CASES_THM)

lemma ALG_COVER_SET_CASES: "ALL P::bool list list => bool.
   P [[]] &
   (ALL (l1::bool list list) l2::bool list list.
       alg_cover_set l1 &
       alg_cover_set l2 &
       alg_cover_set (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2)) -->
   (ALL l::bool list list. alg_cover_set l --> P l)"
  by (import prob_indep ALG_COVER_SET_CASES)

lemma ALG_COVER_SET_INDUCTION: "ALL P::bool list list => bool.
   P [[]] &
   (ALL (l1::bool list list) l2::bool list list.
       alg_cover_set l1 &
       alg_cover_set l2 &
       P l1 &
       P l2 & alg_cover_set (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2)) -->
   (ALL l::bool list list. alg_cover_set l --> P l)"
  by (import prob_indep ALG_COVER_SET_INDUCTION)

lemma ALG_COVER_EXISTS_UNIQUE: "ALL l::bool list list.
   alg_cover_set l -->
   (ALL s::nat => bool. EX! x::bool list. x mem l & alg_embed x s)"
  by (import prob_indep ALG_COVER_EXISTS_UNIQUE)

lemma ALG_COVER_UNIQUE: "ALL (l::bool list list) (x::bool list) s::nat => bool.
   alg_cover_set l & x mem l & alg_embed x s --> alg_cover l s = x"
  by (import prob_indep ALG_COVER_UNIQUE)

lemma ALG_COVER_STEP: "ALL (l1::bool list list) (l2::bool list list) (h::bool) t::nat => bool.
   alg_cover_set l1 & alg_cover_set l2 -->
   alg_cover (map (op # True) l1 @ map (op # False) l2) (SCONS h t) =
   (if h then True # alg_cover l1 t else False # alg_cover l2 t)"
  by (import prob_indep ALG_COVER_STEP)

lemma ALG_COVER_HEAD: "ALL l::bool list list.
   alg_cover_set l -->
   (ALL f::bool list => bool. f o alg_cover l = algebra_embed (filter f l))"
  by (import prob_indep ALG_COVER_HEAD)

lemma ALG_COVER_TAIL_STEP: "ALL (l1::bool list list) (l2::bool list list) q::(nat => bool) => bool.
   alg_cover_set l1 & alg_cover_set l2 -->
   q o
   (%x::nat => bool.
       SDROP
        (length (alg_cover (map (op # True) l1 @ map (op # False) l2) x))
        x) =
   pred_set.UNION
    (pred_set.INTER (%x::nat => bool. SHD x = True)
      (q o ((%x::nat => bool. SDROP (length (alg_cover l1 x)) x) o STL)))
    (pred_set.INTER (%x::nat => bool. SHD x = False)
      (q o ((%x::nat => bool. SDROP (length (alg_cover l2 x)) x) o STL)))"
  by (import prob_indep ALG_COVER_TAIL_STEP)

lemma ALG_COVER_TAIL_MEASURABLE: "ALL l::bool list list.
   alg_cover_set l -->
   (ALL q::(nat => bool) => bool.
       measurable
        (q o (%x::nat => bool. SDROP (length (alg_cover l x)) x)) =
       measurable q)"
  by (import prob_indep ALG_COVER_TAIL_MEASURABLE)

lemma ALG_COVER_TAIL_PROB: "ALL l::bool list list.
   alg_cover_set l -->
   (ALL q::(nat => bool) => bool.
       measurable q -->
       prob (q o (%x::nat => bool. SDROP (length (alg_cover l x)) x)) =
       prob q)"
  by (import prob_indep ALG_COVER_TAIL_PROB)

lemma INDEP_INDEP_SET_LEMMA: "ALL l::bool list list.
   alg_cover_set l -->
   (ALL q::(nat => bool) => bool.
       measurable q -->
       (ALL x::bool list.
           x mem l -->
           prob
            (pred_set.INTER (alg_embed x)
              (q o (%x::nat => bool. SDROP (length (alg_cover l x)) x))) =
           (1 / 2) ^ length x * prob q))"
  by (import prob_indep INDEP_INDEP_SET_LEMMA)

lemma INDEP_SET_LIST: "ALL (q::(nat => bool) => bool) l::bool list list.
   alg_sorted l &
   alg_prefixfree l &
   measurable q &
   (ALL x::bool list. x mem l --> indep_set (alg_embed x) q) -->
   indep_set (algebra_embed l) q"
  by (import prob_indep INDEP_SET_LIST)

lemma INDEP_INDEP_SET: "ALL (f::(nat => bool) => 'a::type * (nat => bool)) (p::'a::type => bool)
   q::(nat => bool) => bool.
   indep f & measurable q --> indep_set (p o (fst o f)) (q o (snd o f))"
  by (import prob_indep INDEP_INDEP_SET)

lemma INDEP_UNIT: "ALL x::'a::type. indep (UNIT x)"
  by (import prob_indep INDEP_UNIT)

lemma INDEP_SDEST: "indep SDEST"
  by (import prob_indep INDEP_SDEST)

lemma BIND_STEP: "ALL f::(nat => bool) => 'a::type * (nat => bool).
   BIND SDEST (%k::bool. f o SCONS k) = f"
  by (import prob_indep BIND_STEP)

lemma INDEP_BIND_SDEST: "ALL f::bool => (nat => bool) => 'a::type * (nat => bool).
   (ALL x::bool. indep (f x)) --> indep (BIND SDEST f)"
  by (import prob_indep INDEP_BIND_SDEST)

lemma INDEP_BIND: "ALL (f::(nat => bool) => 'a::type * (nat => bool))
   g::'a::type => (nat => bool) => 'b::type * (nat => bool).
   indep f & (ALL x::'a::type. indep (g x)) --> indep (BIND f g)"
  by (import prob_indep INDEP_BIND)

lemma INDEP_PROB: "ALL (f::(nat => bool) => 'a::type * (nat => bool)) (p::'a::type => bool)
   q::(nat => bool) => bool.
   indep f & measurable q -->
   prob (pred_set.INTER (p o (fst o f)) (q o (snd o f))) =
   prob (p o (fst o f)) * prob q"
  by (import prob_indep INDEP_PROB)

lemma INDEP_MEASURABLE1: "ALL (f::(nat => bool) => 'a::type * (nat => bool)) p::'a::type => bool.
   indep f --> measurable (p o (fst o f))"
  by (import prob_indep INDEP_MEASURABLE1)

lemma INDEP_MEASURABLE2: "ALL (f::(nat => bool) => 'a::type * (nat => bool)) q::(nat => bool) => bool.
   indep f & measurable q --> measurable (q o (snd o f))"
  by (import prob_indep INDEP_MEASURABLE2)

lemma PROB_INDEP_BOUND: "ALL (f::(nat => bool) => nat * (nat => bool)) n::nat.
   indep f -->
   prob (%s::nat => bool. fst (f s) < Suc n) =
   prob (%s::nat => bool. fst (f s) < n) +
   prob (%s::nat => bool. fst (f s) = n)"
  by (import prob_indep PROB_INDEP_BOUND)

;end_setup

;setup_theory prob_uniform

consts
  unif_bound :: "nat => nat" 

defs
  unif_bound_primdef: "unif_bound ==
WFREC
 (SOME R::nat => nat => bool. WF R & (ALL v::nat. R (Suc v div 2) (Suc v)))
 (%unif_bound::nat => nat.
     nat_case 0 (%v1::nat. Suc (unif_bound (Suc v1 div 2))))"

lemma unif_bound_primitive_def: "unif_bound =
WFREC
 (SOME R::nat => nat => bool. WF R & (ALL v::nat. R (Suc v div 2) (Suc v)))
 (%unif_bound::nat => nat.
     nat_case 0 (%v1::nat. Suc (unif_bound (Suc v1 div 2))))"
  by (import prob_uniform unif_bound_primitive_def)

lemma unif_bound_def: "unif_bound 0 = 0 &
unif_bound (Suc (v::nat)) = Suc (unif_bound (Suc v div 2))"
  by (import prob_uniform unif_bound_def)

lemma unif_bound_ind: "ALL P::nat => bool.
   P 0 & (ALL v::nat. P (Suc v div 2) --> P (Suc v)) --> All P"
  by (import prob_uniform unif_bound_ind)

constdefs
  unif_tupled :: "nat * (nat => bool) => nat * (nat => bool)" 
  "unif_tupled ==
WFREC
 (SOME R::nat * (nat => bool) => nat * (nat => bool) => bool.
     WF R & (ALL (s::nat => bool) v2::nat. R (Suc v2 div 2, s) (Suc v2, s)))
 (%(unif_tupled::nat * (nat => bool) => nat * (nat => bool)) (v::nat,
     v1::nat => bool).
     case v of 0 => (0, v1)
     | Suc (v3::nat) =>
         let (m::nat, s'::nat => bool) = unif_tupled (Suc v3 div 2, v1)
         in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))"

lemma unif_tupled_primitive_def: "unif_tupled =
WFREC
 (SOME R::nat * (nat => bool) => nat * (nat => bool) => bool.
     WF R & (ALL (s::nat => bool) v2::nat. R (Suc v2 div 2, s) (Suc v2, s)))
 (%(unif_tupled::nat * (nat => bool) => nat * (nat => bool)) (v::nat,
     v1::nat => bool).
     case v of 0 => (0, v1)
     | Suc (v3::nat) =>
         let (m::nat, s'::nat => bool) = unif_tupled (Suc v3 div 2, v1)
         in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))"
  by (import prob_uniform unif_tupled_primitive_def)

consts
  unif :: "nat => (nat => bool) => nat * (nat => bool)" 

defs
  unif_primdef: "unif == %(x::nat) x1::nat => bool. unif_tupled (x, x1)"

lemma unif_curried_def: "ALL (x::nat) x1::nat => bool. unif x x1 = unif_tupled (x, x1)"
  by (import prob_uniform unif_curried_def)

lemma unif_def: "unif 0 (s::nat => bool) = (0, s) &
unif (Suc (v2::nat)) s =
(let (m::nat, s'::nat => bool) = unif (Suc v2 div 2) s
 in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))"
  by (import prob_uniform unif_def)

lemma unif_ind: "ALL P::nat => (nat => bool) => bool.
   All (P 0) &
   (ALL (v2::nat) s::nat => bool. P (Suc v2 div 2) s --> P (Suc v2) s) -->
   (ALL v::nat. All (P v))"
  by (import prob_uniform unif_ind)

constdefs
  uniform_tupled :: "nat * nat * (nat => bool) => nat * (nat => bool)" 
  "uniform_tupled ==
WFREC
 (SOME R::nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool.
     WF R &
     (ALL (t::nat) (s::nat => bool) (n::nat) (res::nat) s'::nat => bool.
         (res, s') = unif n s & ~ res < Suc n -->
         R (t, Suc n, s') (Suc t, Suc n, s)))
 (%(uniform_tupled::nat * nat * (nat => bool) => nat * (nat => bool))
     (v::nat, v1::nat * (nat => bool)).
     case v of
     0 => (%(v3::nat, v4::nat => bool).
              case v3 of 0 => ARB | Suc (v5::nat) => (0, v4))
           v1
     | Suc (v2::nat) =>
         (%(v7::nat, v8::nat => bool).
             case v7 of 0 => ARB
             | Suc (v9::nat) =>
                 let (res::nat, s'::nat => bool) = unif v9 v8
                 in if res < Suc v9 then (res, s')
                    else uniform_tupled (v2, Suc v9, s'))
          v1)"

lemma uniform_tupled_primitive_def: "uniform_tupled =
WFREC
 (SOME R::nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool.
     WF R &
     (ALL (t::nat) (s::nat => bool) (n::nat) (res::nat) s'::nat => bool.
         (res, s') = unif n s & ~ res < Suc n -->
         R (t, Suc n, s') (Suc t, Suc n, s)))
 (%(uniform_tupled::nat * nat * (nat => bool) => nat * (nat => bool))
     (v::nat, v1::nat * (nat => bool)).
     case v of
     0 => (%(v3::nat, v4::nat => bool).
              case v3 of 0 => ARB | Suc (v5::nat) => (0, v4))
           v1
     | Suc (v2::nat) =>
         (%(v7::nat, v8::nat => bool).
             case v7 of 0 => ARB
             | Suc (v9::nat) =>
                 let (res::nat, s'::nat => bool) = unif v9 v8
                 in if res < Suc v9 then (res, s')
                    else uniform_tupled (v2, Suc v9, s'))
          v1)"
  by (import prob_uniform uniform_tupled_primitive_def)

consts
  uniform :: "nat => nat => (nat => bool) => nat * (nat => bool)" 

defs
  uniform_primdef: "uniform == %(x::nat) (x1::nat) x2::nat => bool. uniform_tupled (x, x1, x2)"

lemma uniform_curried_def: "ALL (x::nat) (x1::nat) x2::nat => bool.
   uniform x x1 x2 = uniform_tupled (x, x1, x2)"
  by (import prob_uniform uniform_curried_def)

lemma uniform_ind: "ALL P::nat => nat => (nat => bool) => bool.
   (ALL x::nat. All (P (Suc x) 0)) &
   All (P 0 0) &
   (ALL x::nat. All (P 0 (Suc x))) &
   (ALL (x::nat) (xa::nat) xb::nat => bool.
       (ALL (xc::nat) xd::nat => bool.
           (xc, xd) = unif xa xb & ~ xc < Suc xa --> P x (Suc xa) xd) -->
       P (Suc x) (Suc xa) xb) -->
   (ALL (x::nat) xa::nat. All (P x xa))"
  by (import prob_uniform uniform_ind)

lemma uniform_def: "uniform 0 (Suc (n::nat)) (s::nat => bool) = (0, s) &
uniform (Suc (t::nat)) (Suc n) s =
(let (xa::nat, x::nat => bool) = unif n s
 in if xa < Suc n then (xa, x) else uniform t (Suc n) x)"
  by (import prob_uniform uniform_def)

lemma SUC_DIV_TWO_ZERO: "ALL n::nat. (Suc n div 2 = 0) = (n = 0)"
  by (import prob_uniform SUC_DIV_TWO_ZERO)

lemma UNIF_BOUND_LOWER: "ALL n::nat. n < 2 ^ unif_bound n"
  by (import prob_uniform UNIF_BOUND_LOWER)

lemma UNIF_BOUND_LOWER_SUC: "ALL n::nat. Suc n <= 2 ^ unif_bound n"
  by (import prob_uniform UNIF_BOUND_LOWER_SUC)

lemma UNIF_BOUND_UPPER: "ALL n::nat. n ~= 0 --> 2 ^ unif_bound n <= 2 * n"
  by (import prob_uniform UNIF_BOUND_UPPER)

lemma UNIF_BOUND_UPPER_SUC: "ALL n::nat. 2 ^ unif_bound n <= Suc (2 * n)"
  by (import prob_uniform UNIF_BOUND_UPPER_SUC)

lemma UNIF_DEF_MONAD: "unif 0 = UNIT 0 &
(ALL n::nat.
    unif (Suc n) =
    BIND (unif (Suc n div 2))
     (%m::nat.
         BIND SDEST (%b::bool. UNIT (if b then 2 * m + 1 else 2 * m))))"
  by (import prob_uniform UNIF_DEF_MONAD)

lemma UNIFORM_DEF_MONAD: "(ALL x::nat. uniform 0 (Suc x) = UNIT 0) &
(ALL (x::nat) xa::nat.
    uniform (Suc x) (Suc xa) =
    BIND (unif xa)
     (%m::nat. if m < Suc xa then UNIT m else uniform x (Suc xa)))"
  by (import prob_uniform UNIFORM_DEF_MONAD)

lemma INDEP_UNIF: "ALL n::nat. indep (unif n)"
  by (import prob_uniform INDEP_UNIF)

lemma INDEP_UNIFORM: "ALL (t::nat) n::nat. indep (uniform t (Suc n))"
  by (import prob_uniform INDEP_UNIFORM)

lemma PROB_UNIF: "ALL (n::nat) k::nat.
   prob (%s::nat => bool. fst (unif n s) = k) =
   (if k < 2 ^ unif_bound n then (1 / 2) ^ unif_bound n else 0)"
  by (import prob_uniform PROB_UNIF)

lemma UNIF_RANGE: "ALL (n::nat) s::nat => bool. fst (unif n s) < 2 ^ unif_bound n"
  by (import prob_uniform UNIF_RANGE)

lemma PROB_UNIF_PAIR: "ALL (n::nat) (k::nat) k'::nat.
   (prob (%s::nat => bool. fst (unif n s) = k) =
    prob (%s::nat => bool. fst (unif n s) = k')) =
   ((k < 2 ^ unif_bound n) = (k' < 2 ^ unif_bound n))"
  by (import prob_uniform PROB_UNIF_PAIR)

lemma PROB_UNIF_BOUND: "ALL (n::nat) k::nat.
   k <= 2 ^ unif_bound n -->
   prob (%s::nat => bool. fst (unif n s) < k) =
   real k * (1 / 2) ^ unif_bound n"
  by (import prob_uniform PROB_UNIF_BOUND)

lemma PROB_UNIF_GOOD: "ALL n::nat. 1 / 2 <= prob (%s::nat => bool. fst (unif n s) < Suc n)"
  by (import prob_uniform PROB_UNIF_GOOD)

lemma UNIFORM_RANGE: "ALL (t::nat) (n::nat) s::nat => bool. fst (uniform t (Suc n) s) < Suc n"
  by (import prob_uniform UNIFORM_RANGE)

lemma PROB_UNIFORM_LOWER_BOUND: "(All::(real => bool) => bool)
 (%b::real.
     (op -->::bool => bool => bool)
      ((All::(nat => bool) => bool)
        (%k::nat.
            (op -->::bool => bool => bool)
             ((op <::nat => nat => bool) k ((Suc::nat => nat) (n::nat)))
             ((op <::real => real => bool)
               ((prob::((nat => bool) => bool) => real)
                 (%s::nat => bool.
                     (op =::nat => nat => bool)
                      ((fst::nat * (nat => bool) => nat)
                        ((uniform::nat
                                   => nat
=> (nat => bool) => nat * (nat => bool))
                          (t::nat) ((Suc::nat => nat) n) s))
                      k))
               b)))
      ((All::(nat => bool) => bool)
        (%m::nat.
            (op -->::bool => bool => bool)
             ((op <::nat => nat => bool) m ((Suc::nat => nat) n))
             ((op <::real => real => bool)
               ((prob::((nat => bool) => bool) => real)
                 (%s::nat => bool.
                     (op <::nat => nat => bool)
                      ((fst::nat * (nat => bool) => nat)
                        ((uniform::nat
                                   => nat
=> (nat => bool) => nat * (nat => bool))
                          t ((Suc::nat => nat) n) s))
                      ((Suc::nat => nat) m)))
               ((op *::real => real => real)
                 ((real::nat => real) ((Suc::nat => nat) m)) b)))))"
  by (import prob_uniform PROB_UNIFORM_LOWER_BOUND)

lemma PROB_UNIFORM_UPPER_BOUND: "(All::(real => bool) => bool)
 (%b::real.
     (op -->::bool => bool => bool)
      ((All::(nat => bool) => bool)
        (%k::nat.
            (op -->::bool => bool => bool)
             ((op <::nat => nat => bool) k ((Suc::nat => nat) (n::nat)))
             ((op <::real => real => bool) b
               ((prob::((nat => bool) => bool) => real)
                 (%s::nat => bool.
                     (op =::nat => nat => bool)
                      ((fst::nat * (nat => bool) => nat)
                        ((uniform::nat
                                   => nat
=> (nat => bool) => nat * (nat => bool))
                          (t::nat) ((Suc::nat => nat) n) s))
                      k)))))
      ((All::(nat => bool) => bool)
        (%m::nat.
            (op -->::bool => bool => bool)
             ((op <::nat => nat => bool) m ((Suc::nat => nat) n))
             ((op <::real => real => bool)
               ((op *::real => real => real)
                 ((real::nat => real) ((Suc::nat => nat) m)) b)
               ((prob::((nat => bool) => bool) => real)
                 (%s::nat => bool.
                     (op <::nat => nat => bool)
                      ((fst::nat * (nat => bool) => nat)
                        ((uniform::nat
                                   => nat
=> (nat => bool) => nat * (nat => bool))
                          t ((Suc::nat => nat) n) s))
                      ((Suc::nat => nat) m)))))))"
  by (import prob_uniform PROB_UNIFORM_UPPER_BOUND)

lemma PROB_UNIFORM_PAIR_SUC: "ALL (t::nat) (n::nat) (k::nat) k'::nat.
   k < Suc n & k' < Suc n -->
   abs (prob (%s::nat => bool. fst (uniform t (Suc n) s) = k) -
        prob (%s::nat => bool. fst (uniform t (Suc n) s) = k'))
   <= (1 / 2) ^ t"
  by (import prob_uniform PROB_UNIFORM_PAIR_SUC)

lemma PROB_UNIFORM_SUC: "ALL (t::nat) (n::nat) k::nat.
   k < Suc n -->
   abs (prob (%s::nat => bool. fst (uniform t (Suc n) s) = k) -
        1 / real (Suc n))
   <= (1 / 2) ^ t"
  by (import prob_uniform PROB_UNIFORM_SUC)

lemma PROB_UNIFORM: "ALL (t::nat) (n::nat) k::nat.
   k < n -->
   abs (prob (%s::nat => bool. fst (uniform t n s) = k) - 1 / real n)
   <= (1 / 2) ^ t"
  by (import prob_uniform PROB_UNIFORM)

;end_setup

end

