theory HOL4Prob = HOL4Real:

;setup_theory prob_extra

lemma BOOL_BOOL_CASES_THM: "ALL f. f = (%b. False) | f = (%b. True) | f = (%b. b) | f = Not"
  by (import prob_extra BOOL_BOOL_CASES_THM)

lemma EVEN_ODD_BASIC: "EVEN 0 & ~ EVEN 1 & EVEN 2 & ~ ODD 0 & ODD 1 & ~ ODD 2"
  by (import prob_extra EVEN_ODD_BASIC)

lemma EVEN_ODD_EXISTS_EQ: "ALL n. EVEN n = (EX m. n = 2 * m) & ODD n = (EX m. n = Suc (2 * m))"
  by (import prob_extra EVEN_ODD_EXISTS_EQ)

lemma DIV_THEN_MULT: "ALL p q. Suc q * (p div Suc q) <= p"
  by (import prob_extra DIV_THEN_MULT)

lemma DIV_TWO_UNIQUE: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(nat => bool) => bool)
      (%q::nat.
          (All::(nat => bool) => bool)
           (%r::nat.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op =::nat => nat => bool) n
                    ((op +::nat => nat => nat)
                      ((op *::nat => nat => nat)
                        ((number_of::bin => nat)
                          ((op BIT::bin => bool => bin)
                            ((op BIT::bin => bool => bin) (bin.Pls::bin)
                              (True::bool))
                            (False::bool)))
                        q)
                      r))
                  ((op |::bool => bool => bool)
                    ((op =::nat => nat => bool) r (0::nat))
                    ((op =::nat => nat => bool) r (1::nat))))
                ((op &::bool => bool => bool)
                  ((op =::nat => nat => bool) q
                    ((op div::nat => nat => nat) n
                      ((number_of::bin => nat)
                        ((op BIT::bin => bool => bin)
                          ((op BIT::bin => bool => bin) (bin.Pls::bin)
                            (True::bool))
                          (False::bool)))))
                  ((op =::nat => nat => bool) r
                    ((op mod::nat => nat => nat) n
                      ((number_of::bin => nat)
                        ((op BIT::bin => bool => bin)
                          ((op BIT::bin => bool => bin) (bin.Pls::bin)
                            (True::bool))
                          (False::bool)))))))))"
  by (import prob_extra DIV_TWO_UNIQUE)

lemma DIVISION_TWO: "ALL n::nat.
   n = (2::nat) * (n div (2::nat)) + n mod (2::nat) &
   (n mod (2::nat) = (0::nat) | n mod (2::nat) = (1::nat))"
  by (import prob_extra DIVISION_TWO)

lemma DIV_TWO: "ALL n::nat. n = (2::nat) * (n div (2::nat)) + n mod (2::nat)"
  by (import prob_extra DIV_TWO)

lemma MOD_TWO: "ALL n. n mod 2 = (if EVEN n then 0 else 1)"
  by (import prob_extra MOD_TWO)

lemma DIV_TWO_BASIC: "(0::nat) div (2::nat) = (0::nat) &
(1::nat) div (2::nat) = (0::nat) & (2::nat) div (2::nat) = (1::nat)"
  by (import prob_extra DIV_TWO_BASIC)

lemma DIV_TWO_MONO: "(All::(nat => bool) => bool)
 (%m::nat.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool)
           ((op <::nat => nat => bool)
             ((op div::nat => nat => nat) m
               ((number_of::bin => nat)
                 ((op BIT::bin => bool => bin)
                   ((op BIT::bin => bool => bin) (bin.Pls::bin)
                     (True::bool))
                   (False::bool))))
             ((op div::nat => nat => nat) n
               ((number_of::bin => nat)
                 ((op BIT::bin => bool => bin)
                   ((op BIT::bin => bool => bin) (bin.Pls::bin)
                     (True::bool))
                   (False::bool)))))
           ((op <::nat => nat => bool) m n)))"
  by (import prob_extra DIV_TWO_MONO)

lemma DIV_TWO_MONO_EVEN: "(All::(nat => bool) => bool)
 (%m::nat.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool) ((EVEN::nat => bool) n)
           ((op =::bool => bool => bool)
             ((op <::nat => nat => bool)
               ((op div::nat => nat => nat) m
                 ((number_of::bin => nat)
                   ((op BIT::bin => bool => bin)
                     ((op BIT::bin => bool => bin) (bin.Pls::bin)
                       (True::bool))
                     (False::bool))))
               ((op div::nat => nat => nat) n
                 ((number_of::bin => nat)
                   ((op BIT::bin => bool => bin)
                     ((op BIT::bin => bool => bin) (bin.Pls::bin)
                       (True::bool))
                     (False::bool)))))
             ((op <::nat => nat => bool) m n))))"
  by (import prob_extra DIV_TWO_MONO_EVEN)

lemma DIV_TWO_CANCEL: "ALL n. 2 * n div 2 = n & Suc (2 * n) div 2 = n"
  by (import prob_extra DIV_TWO_CANCEL)

lemma EXP_DIV_TWO: "ALL n::nat. (2::nat) ^ Suc n div (2::nat) = (2::nat) ^ n"
  by (import prob_extra EXP_DIV_TWO)

lemma EVEN_EXP_TWO: "ALL n. EVEN (2 ^ n) = (n ~= 0)"
  by (import prob_extra EVEN_EXP_TWO)

lemma DIV_TWO_EXP: "ALL (n::nat) k::nat.
   (k div (2::nat) < (2::nat) ^ n) = (k < (2::nat) ^ Suc n)"
  by (import prob_extra DIV_TWO_EXP)

consts
  inf :: "(real => bool) => real" 

defs
  inf_primdef: "inf == %P. - sup (IMAGE uminus P)"

lemma inf_def: "ALL P. inf P = - sup (IMAGE uminus P)"
  by (import prob_extra inf_def)

lemma INF_DEF_ALT: "ALL P. inf P = - sup (%r. P (- r))"
  by (import prob_extra INF_DEF_ALT)

lemma REAL_SUP_EXISTS_UNIQUE: "(All::((real => bool) => bool) => bool)
 (%P::real => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) ((Ex::(real => bool) => bool) P)
        ((Ex::(real => bool) => bool)
          (%z::real.
              (All::(real => bool) => bool)
               (%x::real.
                   (op -->::bool => bool => bool) (P x)
                    ((op <=::real => real => bool) x z)))))
      ((Ex1::(real => bool) => bool)
        (%s::real.
            (All::(real => bool) => bool)
             (%y::real.
                 (op =::bool => bool => bool)
                  ((Ex::(real => bool) => bool)
                    (%x::real.
                        (op &::bool => bool => bool) (P x)
                         ((op <::real => real => bool) y x)))
                  ((op <::real => real => bool) y s)))))"
  by (import prob_extra REAL_SUP_EXISTS_UNIQUE)

lemma REAL_SUP_MAX: "(All::((real => bool) => bool) => bool)
 (%P::real => bool.
     (All::(real => bool) => bool)
      (%z::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool) (P z)
             ((All::(real => bool) => bool)
               (%x::real.
                   (op -->::bool => bool => bool) (P x)
                    ((op <=::real => real => bool) x z))))
           ((op =::real => real => bool) ((sup::(real => bool) => real) P)
             z)))"
  by (import prob_extra REAL_SUP_MAX)

lemma REAL_INF_MIN: "(All::((real => bool) => bool) => bool)
 (%P::real => bool.
     (All::(real => bool) => bool)
      (%z::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool) (P z)
             ((All::(real => bool) => bool)
               (%x::real.
                   (op -->::bool => bool => bool) (P x)
                    ((op <=::real => real => bool) z x))))
           ((op =::real => real => bool) ((inf::(real => bool) => real) P)
             z)))"
  by (import prob_extra REAL_INF_MIN)

lemma HALF_POS: "(0::real) < (1::real) / (2::real)"
  by (import prob_extra HALF_POS)

lemma HALF_CANCEL: "(2::real) * ((1::real) / (2::real)) = (1::real)"
  by (import prob_extra HALF_CANCEL)

lemma POW_HALF_POS: "ALL n::nat. (0::real) < ((1::real) / (2::real)) ^ n"
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
                   ((op BIT::bin => bool => bin)
                     ((op BIT::bin => bool => bin) (bin.Pls::bin)
                       (True::bool))
                     (False::bool))))
               n)
             ((op ^::real => nat => real)
               ((op /::real => real => real) (1::real)
                 ((number_of::bin => real)
                   ((op BIT::bin => bool => bin)
                     ((op BIT::bin => bool => bin) (bin.Pls::bin)
                       (True::bool))
                     (False::bool))))
               m))))"
  by (import prob_extra POW_HALF_MONO)

lemma POW_HALF_TWICE: "ALL n::nat.
   ((1::real) / (2::real)) ^ n = (2::real) * ((1::real) / (2::real)) ^ Suc n"
  by (import prob_extra POW_HALF_TWICE)

lemma X_HALF_HALF: "ALL x::real. (1::real) / (2::real) * x + (1::real) / (2::real) * x = x"
  by (import prob_extra X_HALF_HALF)

lemma REAL_SUP_LE_X: "(All::((real => bool) => bool) => bool)
 (%P::real => bool.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool) ((Ex::(real => bool) => bool) P)
             ((All::(real => bool) => bool)
               (%r::real.
                   (op -->::bool => bool => bool) (P r)
                    ((op <=::real => real => bool) r x))))
           ((op <=::real => real => bool) ((sup::(real => bool) => real) P)
             x)))"
  by (import prob_extra REAL_SUP_LE_X)

lemma REAL_X_LE_SUP: "(All::((real => bool) => bool) => bool)
 (%P::real => bool.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool) ((Ex::(real => bool) => bool) P)
             ((op &::bool => bool => bool)
               ((Ex::(real => bool) => bool)
                 (%z::real.
                     (All::(real => bool) => bool)
                      (%r::real.
                          (op -->::bool => bool => bool) (P r)
                           ((op <=::real => real => bool) r z))))
               ((Ex::(real => bool) => bool)
                 (%r::real.
                     (op &::bool => bool => bool) (P r)
                      ((op <=::real => real => bool) x r)))))
           ((op <=::real => real => bool) x
             ((sup::(real => bool) => real) P))))"
  by (import prob_extra REAL_X_LE_SUP)

lemma ABS_BETWEEN_LE: "ALL (x::real) (y::real) d::real.
   ((0::real) <= d & x - d <= y & y <= x + d) = (abs (y - x) <= d)"
  by (import prob_extra ABS_BETWEEN_LE)

lemma ONE_MINUS_HALF: "(1::real) - (1::real) / (2::real) = (1::real) / (2::real)"
  by (import prob_extra ONE_MINUS_HALF)

lemma HALF_LT_1: "(1::real) / (2::real) < (1::real)"
  by (import prob_extra HALF_LT_1)

lemma POW_HALF_EXP: "ALL n::nat. ((1::real) / (2::real)) ^ n = inverse (real ((2::nat) ^ n))"
  by (import prob_extra POW_HALF_EXP)

lemma INV_SUC_POS: "ALL n. 0 < 1 / real (Suc n)"
  by (import prob_extra INV_SUC_POS)

lemma INV_SUC_MAX: "ALL x. 1 / real (Suc x) <= 1"
  by (import prob_extra INV_SUC_MAX)

lemma INV_SUC: "ALL n. 0 < 1 / real (Suc n) & 1 / real (Suc n) <= 1"
  by (import prob_extra INV_SUC)

lemma ABS_UNIT_INTERVAL: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <=::real => real => bool) (0::real) x)
             ((op &::bool => bool => bool)
               ((op <=::real => real => bool) x (1::real))
               ((op &::bool => bool => bool)
                 ((op <=::real => real => bool) (0::real) y)
                 ((op <=::real => real => bool) y (1::real)))))
           ((op <=::real => real => bool)
             ((abs::real => real) ((op -::real => real => real) x y))
             (1::real))))"
  by (import prob_extra ABS_UNIT_INTERVAL)

lemma MEM_NIL: "ALL l. (ALL x. ~ x mem l) = (l = [])"
  by (import prob_extra MEM_NIL)

lemma MAP_MEM: "ALL f l x. x mem map f l = (EX y. y mem l & x = f y)"
  by (import prob_extra MAP_MEM)

lemma MEM_NIL_MAP_CONS: "ALL x l. ~ [] mem map (op # x) l"
  by (import prob_extra MEM_NIL_MAP_CONS)

lemma FILTER_TRUE: "ALL l. [x:l. True] = l"
  by (import prob_extra FILTER_TRUE)

lemma FILTER_FALSE: "ALL l. [x:l. False] = []"
  by (import prob_extra FILTER_FALSE)

lemma FILTER_MEM: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (All::('a => bool) => bool)
      (%x::'a.
          (All::('a list => bool) => bool)
           (%l::'a list.
               (op -->::bool => bool => bool)
                ((op mem::'a => 'a list => bool) x
                  ((filter::('a => bool) => 'a list => 'a list) P l))
                (P x))))"
  by (import prob_extra FILTER_MEM)

lemma MEM_FILTER: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (All::('a list => bool) => bool)
      (%l::'a list.
          (All::('a => bool) => bool)
           (%x::'a.
               (op -->::bool => bool => bool)
                ((op mem::'a => 'a list => bool) x
                  ((filter::('a => bool) => 'a list => 'a list) P l))
                ((op mem::'a => 'a list => bool) x l))))"
  by (import prob_extra MEM_FILTER)

lemma FILTER_OUT_ELT: "ALL x l. x mem l | [y:l. y ~= x] = l"
  by (import prob_extra FILTER_OUT_ELT)

lemma IS_PREFIX_NIL: "ALL x. IS_PREFIX x [] & IS_PREFIX [] x = (x = [])"
  by (import prob_extra IS_PREFIX_NIL)

lemma IS_PREFIX_REFL: "ALL x. IS_PREFIX x x"
  by (import prob_extra IS_PREFIX_REFL)

lemma IS_PREFIX_ANTISYM: "(All::('a list => bool) => bool)
 (%x::'a list.
     (All::('a list => bool) => bool)
      (%y::'a list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((IS_PREFIX::'a list => 'a list => bool) y x)
             ((IS_PREFIX::'a list => 'a list => bool) x y))
           ((op =::'a list => 'a list => bool) x y)))"
  by (import prob_extra IS_PREFIX_ANTISYM)

lemma IS_PREFIX_TRANS: "(All::('a list => bool) => bool)
 (%x::'a list.
     (All::('a list => bool) => bool)
      (%y::'a list.
          (All::('a list => bool) => bool)
           (%z::'a list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((IS_PREFIX::'a list => 'a list => bool) x y)
                  ((IS_PREFIX::'a list => 'a list => bool) y z))
                ((IS_PREFIX::'a list => 'a list => bool) x z))))"
  by (import prob_extra IS_PREFIX_TRANS)

lemma IS_PREFIX_BUTLAST: "ALL x y. IS_PREFIX (x # y) (butlast (x # y))"
  by (import prob_extra IS_PREFIX_BUTLAST)

lemma IS_PREFIX_LENGTH: "(All::('a list => bool) => bool)
 (%x::'a list.
     (All::('a list => bool) => bool)
      (%y::'a list.
          (op -->::bool => bool => bool)
           ((IS_PREFIX::'a list => 'a list => bool) y x)
           ((op <=::nat => nat => bool) ((size::'a list => nat) x)
             ((size::'a list => nat) y))))"
  by (import prob_extra IS_PREFIX_LENGTH)

lemma IS_PREFIX_LENGTH_ANTI: "(All::('a list => bool) => bool)
 (%x::'a list.
     (All::('a list => bool) => bool)
      (%y::'a list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((IS_PREFIX::'a list => 'a list => bool) y x)
             ((op =::nat => nat => bool) ((size::'a list => nat) x)
               ((size::'a list => nat) y)))
           ((op =::'a list => 'a list => bool) x y)))"
  by (import prob_extra IS_PREFIX_LENGTH_ANTI)

lemma IS_PREFIX_SNOC: "ALL x y z. IS_PREFIX (SNOC x y) z = (IS_PREFIX y z | z = SNOC x y)"
  by (import prob_extra IS_PREFIX_SNOC)

lemma FOLDR_MAP: "ALL (f::'b => 'c => 'c) (e::'c) (g::'a => 'b) l::'a list.
   foldr f (map g l) e = foldr (%x::'a. f (g x)) l e"
  by (import prob_extra FOLDR_MAP)

lemma LAST_MEM: "ALL h t. last (h # t) mem h # t"
  by (import prob_extra LAST_MEM)

lemma LAST_MAP_CONS: "ALL (b::bool) (h::bool list) t::bool list list.
   EX x::bool list. last (map (op # b) (h # t)) = b # x"
  by (import prob_extra LAST_MAP_CONS)

lemma EXISTS_LONGEST: "(All::('a list => bool) => bool)
 (%x::'a list.
     (All::('a list list => bool) => bool)
      (%y::'a list list.
          (Ex::('a list => bool) => bool)
           (%z::'a list.
               (op &::bool => bool => bool)
                ((op mem::'a list => 'a list list => bool) z
                  ((op #::'a list => 'a list list => 'a list list) x y))
                ((All::('a list => bool) => bool)
                  (%w::'a list.
                      (op -->::bool => bool => bool)
                       ((op mem::'a list => 'a list list => bool) w
                         ((op #::'a list => 'a list list => 'a list list) x
                           y))
                       ((op <=::nat => nat => bool)
                         ((size::'a list => nat) w)
                         ((size::'a list => nat) z)))))))"
  by (import prob_extra EXISTS_LONGEST)

lemma UNION_DEF_ALT: "ALL s t. pred_set.UNION s t = (%x. s x | t x)"
  by (import prob_extra UNION_DEF_ALT)

lemma INTER_UNION_RDISTRIB: "ALL p q r.
   pred_set.INTER (pred_set.UNION p q) r =
   pred_set.UNION (pred_set.INTER p r) (pred_set.INTER q r)"
  by (import prob_extra INTER_UNION_RDISTRIB)

lemma SUBSET_EQ: "ALL x xa. (x = xa) = (SUBSET x xa & SUBSET xa x)"
  by (import prob_extra SUBSET_EQ)

lemma INTER_IS_EMPTY: "ALL s t. (pred_set.INTER s t = EMPTY) = (ALL x. ~ s x | ~ t x)"
  by (import prob_extra INTER_IS_EMPTY)

lemma UNION_DISJOINT_SPLIT: "(All::(('a => bool) => bool) => bool)
 (%s::'a => bool.
     (All::(('a => bool) => bool) => bool)
      (%t::'a => bool.
          (All::(('a => bool) => bool) => bool)
           (%u::'a => bool.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op =::('a => bool) => ('a => bool) => bool)
                    ((pred_set.UNION::('a => bool)
=> ('a => bool) => 'a => bool)
                      s t)
                    ((pred_set.UNION::('a => bool)
=> ('a => bool) => 'a => bool)
                      s u))
                  ((op &::bool => bool => bool)
                    ((op =::('a => bool) => ('a => bool) => bool)
                      ((pred_set.INTER::('a => bool)
  => ('a => bool) => 'a => bool)
                        s t)
                      (EMPTY::'a => bool))
                    ((op =::('a => bool) => ('a => bool) => bool)
                      ((pred_set.INTER::('a => bool)
  => ('a => bool) => 'a => bool)
                        s u)
                      (EMPTY::'a => bool))))
                ((op =::('a => bool) => ('a => bool) => bool) t u))))"
  by (import prob_extra UNION_DISJOINT_SPLIT)

lemma GSPEC_DEF_ALT: "ALL f. GSPEC f = (%v. EX x. (v, True) = f x)"
  by (import prob_extra GSPEC_DEF_ALT)

;end_setup

;setup_theory prob_canon

consts
  alg_twin :: "bool list => bool list => bool" 

defs
  alg_twin_primdef: "alg_twin == %x y. EX l. x = SNOC True l & y = SNOC False l"

lemma alg_twin_def: "ALL x y. alg_twin x y = (EX l. x = SNOC True l & y = SNOC False l)"
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
  alg_order_primdef: "alg_order == %x x1. alg_order_tupled (x, x1)"

lemma alg_order_curried_def: "ALL x x1. alg_order x x1 = alg_order_tupled (x, x1)"
  by (import prob_canon alg_order_curried_def)

lemma alg_order_ind: "(All::((bool list => bool list => bool) => bool) => bool)
 (%P::bool list => bool list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((All::(bool => bool) => bool)
          (%x::bool.
              (All::(bool list => bool) => bool)
               (%xa::bool list.
                   P ([]::bool list)
                    ((op #::bool => bool list => bool list) x xa))))
        ((op &::bool => bool => bool) (P ([]::bool list) ([]::bool list))
          ((op &::bool => bool => bool)
            ((All::(bool => bool) => bool)
              (%x::bool.
                  (All::(bool list => bool) => bool)
                   (%xa::bool list.
                       P ((op #::bool => bool list => bool list) x xa)
                        ([]::bool list))))
            ((All::(bool => bool) => bool)
              (%x::bool.
                  (All::(bool list => bool) => bool)
                   (%xa::bool list.
                       (All::(bool => bool) => bool)
                        (%xb::bool.
                            (All::(bool list => bool) => bool)
                             (%xc::bool list.
                                 (op -->::bool => bool => bool) (P xa xc)
                                  (P ((op #::bool => bool list => bool list)
 x xa)
                                    ((op #::bool => bool list => bool list)
xb xc))))))))))
      ((All::(bool list => bool) => bool)
        (%x::bool list. (All::(bool list => bool) => bool) (P x))))"
  by (import prob_canon alg_order_ind)

lemma alg_order_def: "alg_order [] (v6 # v7) = True &
alg_order [] [] = True &
alg_order (v2 # v3) [] = False &
alg_order (h # t) (h' # t') =
(h = True & h' = False | h = h' & alg_order t t')"
  by (import prob_canon alg_order_def)

consts
  alg_sorted :: "bool list list => bool" 

defs
  alg_sorted_primdef: "alg_sorted ==
WFREC (SOME R. WF R & (ALL x z y. R (y # z) (x # y # z)))
 (%alg_sorted.
     list_case True
      (%v2. list_case True
             (%v6 v7. alg_order v2 v6 & alg_sorted (v6 # v7))))"

lemma alg_sorted_primitive_def: "alg_sorted =
WFREC (SOME R. WF R & (ALL x z y. R (y # z) (x # y # z)))
 (%alg_sorted.
     list_case True
      (%v2. list_case True
             (%v6 v7. alg_order v2 v6 & alg_sorted (v6 # v7))))"
  by (import prob_canon alg_sorted_primitive_def)

lemma alg_sorted_ind: "(All::((bool list list => bool) => bool) => bool)
 (%P::bool list list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((All::(bool list => bool) => bool)
          (%x::bool list.
              (All::(bool list => bool) => bool)
               (%y::bool list.
                   (All::(bool list list => bool) => bool)
                    (%z::bool list list.
                        (op -->::bool => bool => bool)
                         (P ((op #::bool list
                                    => bool list list => bool list list)
                              y z))
                         (P ((op #::bool list
                                    => bool list list => bool list list)
                              x ((op #::bool list
  => bool list list => bool list list)
                                  y z)))))))
        ((op &::bool => bool => bool)
          ((All::(bool list => bool) => bool)
            (%v::bool list.
                P ((op #::bool list => bool list list => bool list list) v
                    ([]::bool list list))))
          (P ([]::bool list list))))
      ((All::(bool list list => bool) => bool) P))"
  by (import prob_canon alg_sorted_ind)

lemma alg_sorted_def: "alg_sorted (x # y # z) = (alg_order x y & alg_sorted (y # z)) &
alg_sorted [v] = True & alg_sorted [] = True"
  by (import prob_canon alg_sorted_def)

consts
  alg_prefixfree :: "bool list list => bool" 

defs
  alg_prefixfree_primdef: "alg_prefixfree ==
WFREC (SOME R. WF R & (ALL x z y. R (y # z) (x # y # z)))
 (%alg_prefixfree.
     list_case True
      (%v2. list_case True
             (%v6 v7. ~ IS_PREFIX v6 v2 & alg_prefixfree (v6 # v7))))"

lemma alg_prefixfree_primitive_def: "alg_prefixfree =
WFREC (SOME R. WF R & (ALL x z y. R (y # z) (x # y # z)))
 (%alg_prefixfree.
     list_case True
      (%v2. list_case True
             (%v6 v7. ~ IS_PREFIX v6 v2 & alg_prefixfree (v6 # v7))))"
  by (import prob_canon alg_prefixfree_primitive_def)

lemma alg_prefixfree_ind: "(All::((bool list list => bool) => bool) => bool)
 (%P::bool list list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((All::(bool list => bool) => bool)
          (%x::bool list.
              (All::(bool list => bool) => bool)
               (%y::bool list.
                   (All::(bool list list => bool) => bool)
                    (%z::bool list list.
                        (op -->::bool => bool => bool)
                         (P ((op #::bool list
                                    => bool list list => bool list list)
                              y z))
                         (P ((op #::bool list
                                    => bool list list => bool list list)
                              x ((op #::bool list
  => bool list list => bool list list)
                                  y z)))))))
        ((op &::bool => bool => bool)
          ((All::(bool list => bool) => bool)
            (%v::bool list.
                P ((op #::bool list => bool list list => bool list list) v
                    ([]::bool list list))))
          (P ([]::bool list list))))
      ((All::(bool list list => bool) => bool) P))"
  by (import prob_canon alg_prefixfree_ind)

lemma alg_prefixfree_def: "alg_prefixfree (x # y # z) = (~ IS_PREFIX y x & alg_prefixfree (y # z)) &
alg_prefixfree [v] = True & alg_prefixfree [] = True"
  by (import prob_canon alg_prefixfree_def)

consts
  alg_twinfree :: "bool list list => bool" 

defs
  alg_twinfree_primdef: "alg_twinfree ==
WFREC (SOME R. WF R & (ALL x z y. R (y # z) (x # y # z)))
 (%alg_twinfree.
     list_case True
      (%v2. list_case True
             (%v6 v7. ~ alg_twin v2 v6 & alg_twinfree (v6 # v7))))"

lemma alg_twinfree_primitive_def: "alg_twinfree =
WFREC (SOME R. WF R & (ALL x z y. R (y # z) (x # y # z)))
 (%alg_twinfree.
     list_case True
      (%v2. list_case True
             (%v6 v7. ~ alg_twin v2 v6 & alg_twinfree (v6 # v7))))"
  by (import prob_canon alg_twinfree_primitive_def)

lemma alg_twinfree_ind: "(All::((bool list list => bool) => bool) => bool)
 (%P::bool list list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((All::(bool list => bool) => bool)
          (%x::bool list.
              (All::(bool list => bool) => bool)
               (%y::bool list.
                   (All::(bool list list => bool) => bool)
                    (%z::bool list list.
                        (op -->::bool => bool => bool)
                         (P ((op #::bool list
                                    => bool list list => bool list list)
                              y z))
                         (P ((op #::bool list
                                    => bool list list => bool list list)
                              x ((op #::bool list
  => bool list list => bool list list)
                                  y z)))))))
        ((op &::bool => bool => bool)
          ((All::(bool list => bool) => bool)
            (%v::bool list.
                P ((op #::bool list => bool list list => bool list list) v
                    ([]::bool list list))))
          (P ([]::bool list list))))
      ((All::(bool list list => bool) => bool) P))"
  by (import prob_canon alg_twinfree_ind)

lemma alg_twinfree_def: "alg_twinfree (x # y # z) = (~ alg_twin x y & alg_twinfree (y # z)) &
alg_twinfree [v] = True & alg_twinfree [] = True"
  by (import prob_canon alg_twinfree_def)

consts
  alg_longest :: "bool list list => nat" 

defs
  alg_longest_primdef: "alg_longest == FOLDR (%h t. if t <= length h then length h else t) 0"

lemma alg_longest_def: "alg_longest = FOLDR (%h t. if t <= length h then length h else t) 0"
  by (import prob_canon alg_longest_def)

consts
  alg_canon_prefs :: "bool list => bool list list => bool list list" 

specification (alg_canon_prefs_primdef: alg_canon_prefs) alg_canon_prefs_def: "(ALL l. alg_canon_prefs l [] = [l]) &
(ALL l h t.
    alg_canon_prefs l (h # t) =
    (if IS_PREFIX h l then alg_canon_prefs l t else l # h # t))"
  by (import prob_canon alg_canon_prefs_def)

consts
  alg_canon_find :: "bool list => bool list list => bool list list" 

specification (alg_canon_find_primdef: alg_canon_find) alg_canon_find_def: "(ALL l. alg_canon_find l [] = [l]) &
(ALL l h t.
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

specification (alg_canon_merge_primdef: alg_canon_merge) alg_canon_merge_def: "(ALL l. alg_canon_merge l [] = [l]) &
(ALL l h t.
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
  alg_canon_primdef: "alg_canon == %l. alg_canon2 (alg_canon1 l)"

lemma alg_canon_def: "ALL l. alg_canon l = alg_canon2 (alg_canon1 l)"
  by (import prob_canon alg_canon_def)

consts
  algebra_canon :: "bool list list => bool" 

defs
  algebra_canon_primdef: "algebra_canon == %l. alg_canon l = l"

lemma algebra_canon_def: "ALL l. algebra_canon l = (alg_canon l = l)"
  by (import prob_canon algebra_canon_def)

lemma ALG_TWIN_NIL: "ALL l. ~ alg_twin l [] & ~ alg_twin [] l"
  by (import prob_canon ALG_TWIN_NIL)

lemma ALG_TWIN_SING: "ALL x l.
   alg_twin [x] l = (x = True & l = [False]) &
   alg_twin l [x] = (l = [True] & x = False)"
  by (import prob_canon ALG_TWIN_SING)

lemma ALG_TWIN_CONS: "ALL x y z h t.
   alg_twin (x # y # z) (h # t) = (x = h & alg_twin (y # z) t) &
   alg_twin (h # t) (x # y # z) = (x = h & alg_twin t (y # z))"
  by (import prob_canon ALG_TWIN_CONS)

lemma ALG_TWIN_REDUCE: "ALL h t t'. alg_twin (h # t) (h # t') = alg_twin t t'"
  by (import prob_canon ALG_TWIN_REDUCE)

lemma ALG_TWINS_PREFIX: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%l::bool list.
          (op -->::bool => bool => bool)
           ((IS_PREFIX::bool list => bool list => bool) x l)
           ((op |::bool => bool => bool)
             ((op =::bool list => bool list => bool) x l)
             ((op |::bool => bool => bool)
               ((IS_PREFIX::bool list => bool list => bool) x
                 ((SNOC::bool => bool list => bool list) (True::bool) l))
               ((IS_PREFIX::bool list => bool list => bool) x
                 ((SNOC::bool => bool list => bool list) (False::bool)
                   l))))))"
  by (import prob_canon ALG_TWINS_PREFIX)

lemma ALG_ORDER_NIL: "ALL x. alg_order [] x & alg_order x [] = (x = [])"
  by (import prob_canon ALG_ORDER_NIL)

lemma ALG_ORDER_REFL: "ALL x. alg_order x x"
  by (import prob_canon ALG_ORDER_REFL)

lemma ALG_ORDER_ANTISYM: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_order::bool list => bool list => bool) x y)
             ((alg_order::bool list => bool list => bool) y x))
           ((op =::bool list => bool list => bool) x y)))"
  by (import prob_canon ALG_ORDER_ANTISYM)

lemma ALG_ORDER_TRANS: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (All::(bool list => bool) => bool)
           (%z::bool list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((alg_order::bool list => bool list => bool) x y)
                  ((alg_order::bool list => bool list => bool) y z))
                ((alg_order::bool list => bool list => bool) x z))))"
  by (import prob_canon ALG_ORDER_TRANS)

lemma ALG_ORDER_TOTAL: "ALL x y. alg_order x y | alg_order y x"
  by (import prob_canon ALG_ORDER_TOTAL)

lemma ALG_ORDER_PREFIX: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (op -->::bool => bool => bool)
           ((IS_PREFIX::bool list => bool list => bool) y x)
           ((alg_order::bool list => bool list => bool) x y)))"
  by (import prob_canon ALG_ORDER_PREFIX)

lemma ALG_ORDER_PREFIX_ANTI: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_order::bool list => bool list => bool) x y)
             ((IS_PREFIX::bool list => bool list => bool) x y))
           ((op =::bool list => bool list => bool) x y)))"
  by (import prob_canon ALG_ORDER_PREFIX_ANTI)

lemma ALG_ORDER_PREFIX_MONO: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (All::(bool list => bool) => bool)
           (%z::bool list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((alg_order::bool list => bool list => bool) x y)
                  ((op &::bool => bool => bool)
                    ((alg_order::bool list => bool list => bool) y z)
                    ((IS_PREFIX::bool list => bool list => bool) z x)))
                ((IS_PREFIX::bool list => bool list => bool) y x))))"
  by (import prob_canon ALG_ORDER_PREFIX_MONO)

lemma ALG_ORDER_PREFIX_TRANS: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (All::(bool list => bool) => bool)
           (%z::bool list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((alg_order::bool list => bool list => bool) x y)
                  ((IS_PREFIX::bool list => bool list => bool) y z))
                ((op |::bool => bool => bool)
                  ((alg_order::bool list => bool list => bool) x z)
                  ((IS_PREFIX::bool list => bool list => bool) x z)))))"
  by (import prob_canon ALG_ORDER_PREFIX_TRANS)

lemma ALG_ORDER_SNOC: "ALL x l. ~ alg_order (SNOC x l) l"
  by (import prob_canon ALG_ORDER_SNOC)

lemma ALG_SORTED_MIN: "(All::(bool list => bool) => bool)
 (%h::bool list.
     (All::(bool list list => bool) => bool)
      (%t::bool list list.
          (op -->::bool => bool => bool)
           ((alg_sorted::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) h t))
           ((All::(bool list => bool) => bool)
             (%x::bool list.
                 (op -->::bool => bool => bool)
                  ((op mem::bool list => bool list list => bool) x t)
                  ((alg_order::bool list => bool list => bool) h x)))))"
  by (import prob_canon ALG_SORTED_MIN)

lemma ALG_SORTED_DEF_ALT: "(All::(bool list => bool) => bool)
 (%h::bool list.
     (All::(bool list list => bool) => bool)
      (%t::bool list list.
          (op =::bool => bool => bool)
           ((alg_sorted::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) h t))
           ((op &::bool => bool => bool)
             ((All::(bool list => bool) => bool)
               (%x::bool list.
                   (op -->::bool => bool => bool)
                    ((op mem::bool list => bool list list => bool) x t)
                    ((alg_order::bool list => bool list => bool) h x)))
             ((alg_sorted::bool list list => bool) t))))"
  by (import prob_canon ALG_SORTED_DEF_ALT)

lemma ALG_SORTED_TL: "(All::(bool list => bool) => bool)
 (%h::bool list.
     (All::(bool list list => bool) => bool)
      (%t::bool list list.
          (op -->::bool => bool => bool)
           ((alg_sorted::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) h t))
           ((alg_sorted::bool list list => bool) t)))"
  by (import prob_canon ALG_SORTED_TL)

lemma ALG_SORTED_MONO: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (All::(bool list list => bool) => bool)
           (%z::bool list list.
               (op -->::bool => bool => bool)
                ((alg_sorted::bool list list => bool)
                  ((op #::bool list => bool list list => bool list list) x
                    ((op #::bool list => bool list list => bool list list) y
                      z)))
                ((alg_sorted::bool list list => bool)
                  ((op #::bool list => bool list list => bool list list) x
                    z)))))"
  by (import prob_canon ALG_SORTED_MONO)

lemma ALG_SORTED_TLS: "ALL l b. alg_sorted (map (op # b) l) = alg_sorted l"
  by (import prob_canon ALG_SORTED_TLS)

lemma ALG_SORTED_STEP: "ALL l1 l2.
   alg_sorted (map (op # True) l1 @ map (op # False) l2) =
   (alg_sorted l1 & alg_sorted l2)"
  by (import prob_canon ALG_SORTED_STEP)

lemma ALG_SORTED_APPEND: "ALL h h' t t'.
   alg_sorted ((h # t) @ h' # t') =
   (alg_sorted (h # t) & alg_sorted (h' # t') & alg_order (last (h # t)) h')"
  by (import prob_canon ALG_SORTED_APPEND)

lemma ALG_SORTED_FILTER: "(All::((bool list => bool) => bool) => bool)
 (%P::bool list => bool.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((alg_sorted::bool list list => bool) b)
           ((alg_sorted::bool list list => bool)
             ((filter::(bool list => bool)
                       => bool list list => bool list list)
               P b))))"
  by (import prob_canon ALG_SORTED_FILTER)

lemma ALG_PREFIXFREE_TL: "(All::(bool list => bool) => bool)
 (%h::bool list.
     (All::(bool list list => bool) => bool)
      (%t::bool list list.
          (op -->::bool => bool => bool)
           ((alg_prefixfree::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) h t))
           ((alg_prefixfree::bool list list => bool) t)))"
  by (import prob_canon ALG_PREFIXFREE_TL)

lemma ALG_PREFIXFREE_MONO: "(All::(bool list => bool) => bool)
 (%x::bool list.
     (All::(bool list => bool) => bool)
      (%y::bool list.
          (All::(bool list list => bool) => bool)
           (%z::bool list list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((alg_sorted::bool list list => bool)
                    ((op #::bool list => bool list list => bool list list) x
                      ((op #::bool list => bool list list => bool list list)
                        y z)))
                  ((alg_prefixfree::bool list list => bool)
                    ((op #::bool list => bool list list => bool list list) x
                      ((op #::bool list => bool list list => bool list list)
                        y z))))
                ((alg_prefixfree::bool list list => bool)
                  ((op #::bool list => bool list list => bool list list) x
                    z)))))"
  by (import prob_canon ALG_PREFIXFREE_MONO)

lemma ALG_PREFIXFREE_ELT: "(All::(bool list => bool) => bool)
 (%h::bool list.
     (All::(bool list list => bool) => bool)
      (%t::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool)
               ((op #::bool list => bool list list => bool list list) h t))
             ((alg_prefixfree::bool list list => bool)
               ((op #::bool list => bool list list => bool list list) h t)))
           ((All::(bool list => bool) => bool)
             (%x::bool list.
                 (op -->::bool => bool => bool)
                  ((op mem::bool list => bool list list => bool) x t)
                  ((op &::bool => bool => bool)
                    ((Not::bool => bool)
                      ((IS_PREFIX::bool list => bool list => bool) x h))
                    ((Not::bool => bool)
                      ((IS_PREFIX::bool list => bool list => bool) h
                        x)))))))"
  by (import prob_canon ALG_PREFIXFREE_ELT)

lemma ALG_PREFIXFREE_TLS: "ALL l b. alg_prefixfree (map (op # b) l) = alg_prefixfree l"
  by (import prob_canon ALG_PREFIXFREE_TLS)

lemma ALG_PREFIXFREE_STEP: "ALL l1 l2.
   alg_prefixfree (map (op # True) l1 @ map (op # False) l2) =
   (alg_prefixfree l1 & alg_prefixfree l2)"
  by (import prob_canon ALG_PREFIXFREE_STEP)

lemma ALG_PREFIXFREE_APPEND: "ALL h h' t t'.
   alg_prefixfree ((h # t) @ h' # t') =
   (alg_prefixfree (h # t) &
    alg_prefixfree (h' # t') & ~ IS_PREFIX h' (last (h # t)))"
  by (import prob_canon ALG_PREFIXFREE_APPEND)

lemma ALG_PREFIXFREE_FILTER: "(All::((bool list => bool) => bool) => bool)
 (%P::bool list => bool.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool) b)
             ((alg_prefixfree::bool list list => bool) b))
           ((alg_prefixfree::bool list list => bool)
             ((filter::(bool list => bool)
                       => bool list list => bool list list)
               P b))))"
  by (import prob_canon ALG_PREFIXFREE_FILTER)

lemma ALG_TWINFREE_TL: "(All::(bool list => bool) => bool)
 (%h::bool list.
     (All::(bool list list => bool) => bool)
      (%t::bool list list.
          (op -->::bool => bool => bool)
           ((alg_twinfree::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) h t))
           ((alg_twinfree::bool list list => bool) t)))"
  by (import prob_canon ALG_TWINFREE_TL)

lemma ALG_TWINFREE_TLS: "ALL l b. alg_twinfree (map (op # b) l) = alg_twinfree l"
  by (import prob_canon ALG_TWINFREE_TLS)

lemma ALG_TWINFREE_STEP1: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (op -->::bool => bool => bool)
           ((alg_twinfree::bool list list => bool)
             ((op @::bool list list => bool list list => bool list list)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (True::bool)) l1)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (False::bool))
                 l2)))
           ((op &::bool => bool => bool)
             ((alg_twinfree::bool list list => bool) l1)
             ((alg_twinfree::bool list list => bool) l2))))"
  by (import prob_canon ALG_TWINFREE_STEP1)

lemma ALG_TWINFREE_STEP2: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op |::bool => bool => bool)
               ((Not::bool => bool)
                 ((op mem::bool list => bool list list => bool)
                   ([]::bool list) l1))
               ((Not::bool => bool)
                 ((op mem::bool list => bool list list => bool)
                   ([]::bool list) l2)))
             ((op &::bool => bool => bool)
               ((alg_twinfree::bool list list => bool) l1)
               ((alg_twinfree::bool list list => bool) l2)))
           ((alg_twinfree::bool list list => bool)
             ((op @::bool list list => bool list list => bool list list)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (True::bool)) l1)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (False::bool))
                 l2)))))"
  by (import prob_canon ALG_TWINFREE_STEP2)

lemma ALG_TWINFREE_STEP: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (op -->::bool => bool => bool)
           ((op |::bool => bool => bool)
             ((Not::bool => bool)
               ((op mem::bool list => bool list list => bool)
                 ([]::bool list) l1))
             ((Not::bool => bool)
               ((op mem::bool list => bool list list => bool)
                 ([]::bool list) l2)))
           ((op =::bool => bool => bool)
             ((alg_twinfree::bool list list => bool)
               ((op @::bool list list => bool list list => bool list list)
                 ((map::(bool list => bool list)
                        => bool list list => bool list list)
                   ((op #::bool => bool list => bool list) (True::bool)) l1)
                 ((map::(bool list => bool list)
                        => bool list list => bool list list)
                   ((op #::bool => bool list => bool list) (False::bool))
                   l2)))
             ((op &::bool => bool => bool)
               ((alg_twinfree::bool list list => bool) l1)
               ((alg_twinfree::bool list list => bool) l2)))))"
  by (import prob_canon ALG_TWINFREE_STEP)

lemma ALG_LONGEST_HD: "ALL h t. length h <= alg_longest (h # t)"
  by (import prob_canon ALG_LONGEST_HD)

lemma ALG_LONGEST_TL: "ALL h t. alg_longest t <= alg_longest (h # t)"
  by (import prob_canon ALG_LONGEST_TL)

lemma ALG_LONGEST_TLS: "ALL h t b. alg_longest (map (op # b) (h # t)) = Suc (alg_longest (h # t))"
  by (import prob_canon ALG_LONGEST_TLS)

lemma ALG_LONGEST_APPEND: "ALL l1 l2.
   alg_longest l1 <= alg_longest (l1 @ l2) &
   alg_longest l2 <= alg_longest (l1 @ l2)"
  by (import prob_canon ALG_LONGEST_APPEND)

lemma ALG_CANON_PREFS_HD: "ALL l b. hd (alg_canon_prefs l b) = l"
  by (import prob_canon ALG_CANON_PREFS_HD)

lemma ALG_CANON_PREFS_DELETES: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (All::(bool list => bool) => bool)
           (%x::bool list.
               (op -->::bool => bool => bool)
                ((op mem::bool list => bool list list => bool) x
                  ((alg_canon_prefs::bool list
                                     => bool list list => bool list list)
                    l b))
                ((op mem::bool list => bool list list => bool) x
                  ((op #::bool list => bool list list => bool list list) l
                    b)))))"
  by (import prob_canon ALG_CANON_PREFS_DELETES)

lemma ALG_CANON_PREFS_SORTED: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((alg_sorted::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) l b))
           ((alg_sorted::bool list list => bool)
             ((alg_canon_prefs::bool list
                                => bool list list => bool list list)
               l b))))"
  by (import prob_canon ALG_CANON_PREFS_SORTED)

lemma ALG_CANON_PREFS_PREFIXFREE: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool) b)
             ((alg_prefixfree::bool list list => bool) b))
           ((alg_prefixfree::bool list list => bool)
             ((alg_canon_prefs::bool list
                                => bool list list => bool list list)
               l b))))"
  by (import prob_canon ALG_CANON_PREFS_PREFIXFREE)

lemma ALG_CANON_PREFS_CONSTANT: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((alg_prefixfree::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) l b))
           ((op =::bool list list => bool list list => bool)
             ((alg_canon_prefs::bool list
                                => bool list list => bool list list)
               l b)
             ((op #::bool list => bool list list => bool list list) l b))))"
  by (import prob_canon ALG_CANON_PREFS_CONSTANT)

lemma ALG_CANON_FIND_HD: "ALL l h t.
   hd (alg_canon_find l (h # t)) = l | hd (alg_canon_find l (h # t)) = h"
  by (import prob_canon ALG_CANON_FIND_HD)

lemma ALG_CANON_FIND_DELETES: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (All::(bool list => bool) => bool)
           (%x::bool list.
               (op -->::bool => bool => bool)
                ((op mem::bool list => bool list list => bool) x
                  ((alg_canon_find::bool list
                                    => bool list list => bool list list)
                    l b))
                ((op mem::bool list => bool list list => bool) x
                  ((op #::bool list => bool list list => bool list list) l
                    b)))))"
  by (import prob_canon ALG_CANON_FIND_DELETES)

lemma ALG_CANON_FIND_SORTED: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((alg_sorted::bool list list => bool) b)
           ((alg_sorted::bool list list => bool)
             ((alg_canon_find::bool list
                               => bool list list => bool list list)
               l b))))"
  by (import prob_canon ALG_CANON_FIND_SORTED)

lemma ALG_CANON_FIND_PREFIXFREE: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool) b)
             ((alg_prefixfree::bool list list => bool) b))
           ((alg_prefixfree::bool list list => bool)
             ((alg_canon_find::bool list
                               => bool list list => bool list list)
               l b))))"
  by (import prob_canon ALG_CANON_FIND_PREFIXFREE)

lemma ALG_CANON_FIND_CONSTANT: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool)
               ((op #::bool list => bool list list => bool list list) l b))
             ((alg_prefixfree::bool list list => bool)
               ((op #::bool list => bool list list => bool list list) l b)))
           ((op =::bool list list => bool list list => bool)
             ((alg_canon_find::bool list
                               => bool list list => bool list list)
               l b)
             ((op #::bool list => bool list list => bool list list) l b))))"
  by (import prob_canon ALG_CANON_FIND_CONSTANT)

lemma ALG_CANON1_SORTED: "ALL x. alg_sorted (alg_canon1 x)"
  by (import prob_canon ALG_CANON1_SORTED)

lemma ALG_CANON1_PREFIXFREE: "ALL l. alg_prefixfree (alg_canon1 l)"
  by (import prob_canon ALG_CANON1_PREFIXFREE)

lemma ALG_CANON1_CONSTANT: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) ((alg_sorted::bool list list => bool) l)
        ((alg_prefixfree::bool list list => bool) l))
      ((op =::bool list list => bool list list => bool)
        ((alg_canon1::bool list list => bool list list) l) l))"
  by (import prob_canon ALG_CANON1_CONSTANT)

lemma ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool)
               ((op #::bool list => bool list list => bool list list) l b))
             ((op &::bool => bool => bool)
               ((alg_prefixfree::bool list list => bool)
                 ((op #::bool list => bool list list => bool list list) l
                   b))
               ((alg_twinfree::bool list list => bool) b)))
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool)
               ((alg_canon_merge::bool list
                                  => bool list list => bool list list)
                 l b))
             ((op &::bool => bool => bool)
               ((alg_prefixfree::bool list list => bool)
                 ((alg_canon_merge::bool list
                                    => bool list list => bool list list)
                   l b))
               ((alg_twinfree::bool list list => bool)
                 ((alg_canon_merge::bool list
                                    => bool list list => bool list list)
                   l b))))))"
  by (import prob_canon ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON_MERGE_PREFIXFREE_PRESERVE: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (All::(bool list => bool) => bool)
           (%h::bool list.
               (op -->::bool => bool => bool)
                ((All::(bool list => bool) => bool)
                  (%x::bool list.
                      (op -->::bool => bool => bool)
                       ((op mem::bool list => bool list list => bool) x
                         ((op #::bool list
                                 => bool list list => bool list list)
                           l b))
                       ((op &::bool => bool => bool)
                         ((Not::bool => bool)
                           ((IS_PREFIX::bool list => bool list => bool) h
                             x))
                         ((Not::bool => bool)
                           ((IS_PREFIX::bool list => bool list => bool) x
                             h)))))
                ((All::(bool list => bool) => bool)
                  (%x::bool list.
                      (op -->::bool => bool => bool)
                       ((op mem::bool list => bool list list => bool) x
                         ((alg_canon_merge::bool list
      => bool list list => bool list list)
                           l b))
                       ((op &::bool => bool => bool)
                         ((Not::bool => bool)
                           ((IS_PREFIX::bool list => bool list => bool) h
                             x))
                         ((Not::bool => bool)
                           ((IS_PREFIX::bool list => bool list => bool) x
                             h))))))))"
  by (import prob_canon ALG_CANON_MERGE_PREFIXFREE_PRESERVE)

lemma ALG_CANON_MERGE_SHORTENS: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (All::(bool list => bool) => bool)
           (%x::bool list.
               (op -->::bool => bool => bool)
                ((op mem::bool list => bool list list => bool) x
                  ((alg_canon_merge::bool list
                                     => bool list list => bool list list)
                    l b))
                ((Ex::(bool list => bool) => bool)
                  (%y::bool list.
                      (op &::bool => bool => bool)
                       ((op mem::bool list => bool list list => bool) y
                         ((op #::bool list
                                 => bool list list => bool list list)
                           l b))
                       ((IS_PREFIX::bool list => bool list => bool) y
                         x))))))"
  by (import prob_canon ALG_CANON_MERGE_SHORTENS)

lemma ALG_CANON_MERGE_CONSTANT: "(All::(bool list => bool) => bool)
 (%l::bool list.
     (All::(bool list list => bool) => bool)
      (%b::bool list list.
          (op -->::bool => bool => bool)
           ((alg_twinfree::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) l b))
           ((op =::bool list list => bool list list => bool)
             ((alg_canon_merge::bool list
                                => bool list list => bool list list)
               l b)
             ((op #::bool list => bool list list => bool list list) l b))))"
  by (import prob_canon ALG_CANON_MERGE_CONSTANT)

lemma ALG_CANON2_PREFIXFREE_PRESERVE: "(All::(bool list list => bool) => bool)
 (%x::bool list list.
     (All::(bool list => bool) => bool)
      (%xa::bool list.
          (op -->::bool => bool => bool)
           ((All::(bool list => bool) => bool)
             (%xb::bool list.
                 (op -->::bool => bool => bool)
                  ((op mem::bool list => bool list list => bool) xb x)
                  ((op &::bool => bool => bool)
                    ((Not::bool => bool)
                      ((IS_PREFIX::bool list => bool list => bool) xa xb))
                    ((Not::bool => bool)
                      ((IS_PREFIX::bool list => bool list => bool) xb
                        xa)))))
           ((All::(bool list => bool) => bool)
             (%xb::bool list.
                 (op -->::bool => bool => bool)
                  ((op mem::bool list => bool list list => bool) xb
                    ((alg_canon2::bool list list => bool list list) x))
                  ((op &::bool => bool => bool)
                    ((Not::bool => bool)
                      ((IS_PREFIX::bool list => bool list => bool) xa xb))
                    ((Not::bool => bool)
                      ((IS_PREFIX::bool list => bool list => bool) xb
                        xa)))))))"
  by (import prob_canon ALG_CANON2_PREFIXFREE_PRESERVE)

lemma ALG_CANON2_SHORTENS: "(All::(bool list list => bool) => bool)
 (%x::bool list list.
     (All::(bool list => bool) => bool)
      (%xa::bool list.
          (op -->::bool => bool => bool)
           ((op mem::bool list => bool list list => bool) xa
             ((alg_canon2::bool list list => bool list list) x))
           ((Ex::(bool list => bool) => bool)
             (%y::bool list.
                 (op &::bool => bool => bool)
                  ((op mem::bool list => bool list list => bool) y x)
                  ((IS_PREFIX::bool list => bool list => bool) y xa)))))"
  by (import prob_canon ALG_CANON2_SHORTENS)

lemma ALG_CANON2_SORTED_PREFIXFREE_TWINFREE: "(All::(bool list list => bool) => bool)
 (%x::bool list list.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) ((alg_sorted::bool list list => bool) x)
        ((alg_prefixfree::bool list list => bool) x))
      ((op &::bool => bool => bool)
        ((alg_sorted::bool list list => bool)
          ((alg_canon2::bool list list => bool list list) x))
        ((op &::bool => bool => bool)
          ((alg_prefixfree::bool list list => bool)
            ((alg_canon2::bool list list => bool list list) x))
          ((alg_twinfree::bool list list => bool)
            ((alg_canon2::bool list list => bool list list) x)))))"
  by (import prob_canon ALG_CANON2_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON2_CONSTANT: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((alg_twinfree::bool list list => bool) l)
      ((op =::bool list list => bool list list => bool)
        ((alg_canon2::bool list list => bool list list) l) l))"
  by (import prob_canon ALG_CANON2_CONSTANT)

lemma ALG_CANON_SORTED_PREFIXFREE_TWINFREE: "ALL l.
   alg_sorted (alg_canon l) &
   alg_prefixfree (alg_canon l) & alg_twinfree (alg_canon l)"
  by (import prob_canon ALG_CANON_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON_CONSTANT: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) ((alg_sorted::bool list list => bool) l)
        ((op &::bool => bool => bool)
          ((alg_prefixfree::bool list list => bool) l)
          ((alg_twinfree::bool list list => bool) l)))
      ((op =::bool list list => bool list list => bool)
        ((alg_canon::bool list list => bool list list) l) l))"
  by (import prob_canon ALG_CANON_CONSTANT)

lemma ALG_CANON_IDEMPOT: "ALL l. alg_canon (alg_canon l) = alg_canon l"
  by (import prob_canon ALG_CANON_IDEMPOT)

lemma ALGEBRA_CANON_DEF_ALT: "ALL l. algebra_canon l = (alg_sorted l & alg_prefixfree l & alg_twinfree l)"
  by (import prob_canon ALGEBRA_CANON_DEF_ALT)

lemma ALGEBRA_CANON_BASIC: "algebra_canon [] & algebra_canon [[]] & (ALL x. algebra_canon [x])"
  by (import prob_canon ALGEBRA_CANON_BASIC)

lemma ALG_CANON_BASIC: "alg_canon [] = [] & alg_canon [[]] = [[]] & (ALL x. alg_canon [x] = [x])"
  by (import prob_canon ALG_CANON_BASIC)

lemma ALGEBRA_CANON_TL: "(All::(bool list => bool) => bool)
 (%h::bool list.
     (All::(bool list list => bool) => bool)
      (%t::bool list list.
          (op -->::bool => bool => bool)
           ((algebra_canon::bool list list => bool)
             ((op #::bool list => bool list list => bool list list) h t))
           ((algebra_canon::bool list list => bool) t)))"
  by (import prob_canon ALGEBRA_CANON_TL)

lemma ALGEBRA_CANON_NIL_MEM: "ALL l. (algebra_canon l & [] mem l) = (l = [[]])"
  by (import prob_canon ALGEBRA_CANON_NIL_MEM)

lemma ALGEBRA_CANON_TLS: "ALL l b. algebra_canon (map (op # b) l) = algebra_canon l"
  by (import prob_canon ALGEBRA_CANON_TLS)

lemma ALGEBRA_CANON_STEP1: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (op -->::bool => bool => bool)
           ((algebra_canon::bool list list => bool)
             ((op @::bool list list => bool list list => bool list list)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (True::bool)) l1)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (False::bool))
                 l2)))
           ((op &::bool => bool => bool)
             ((algebra_canon::bool list list => bool) l1)
             ((algebra_canon::bool list list => bool) l2))))"
  by (import prob_canon ALGEBRA_CANON_STEP1)

lemma ALGEBRA_CANON_STEP2: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op |::bool => bool => bool)
               ((Not::bool => bool)
                 ((op =::bool list list => bool list list => bool) l1
                   ((op #::bool list => bool list list => bool list list)
                     ([]::bool list) ([]::bool list list))))
               ((Not::bool => bool)
                 ((op =::bool list list => bool list list => bool) l2
                   ((op #::bool list => bool list list => bool list list)
                     ([]::bool list) ([]::bool list list)))))
             ((op &::bool => bool => bool)
               ((algebra_canon::bool list list => bool) l1)
               ((algebra_canon::bool list list => bool) l2)))
           ((algebra_canon::bool list list => bool)
             ((op @::bool list list => bool list list => bool list list)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (True::bool)) l1)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 ((op #::bool => bool list => bool list) (False::bool))
                 l2)))))"
  by (import prob_canon ALGEBRA_CANON_STEP2)

lemma ALGEBRA_CANON_STEP: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (op -->::bool => bool => bool)
           ((op |::bool => bool => bool)
             ((Not::bool => bool)
               ((op =::bool list list => bool list list => bool) l1
                 ((op #::bool list => bool list list => bool list list)
                   ([]::bool list) ([]::bool list list))))
             ((Not::bool => bool)
               ((op =::bool list list => bool list list => bool) l2
                 ((op #::bool list => bool list list => bool list list)
                   ([]::bool list) ([]::bool list list)))))
           ((op =::bool => bool => bool)
             ((algebra_canon::bool list list => bool)
               ((op @::bool list list => bool list list => bool list list)
                 ((map::(bool list => bool list)
                        => bool list list => bool list list)
                   ((op #::bool => bool list => bool list) (True::bool)) l1)
                 ((map::(bool list => bool list)
                        => bool list list => bool list list)
                   ((op #::bool => bool list => bool list) (False::bool))
                   l2)))
             ((op &::bool => bool => bool)
               ((algebra_canon::bool list list => bool) l1)
               ((algebra_canon::bool list list => bool) l2)))))"
  by (import prob_canon ALGEBRA_CANON_STEP)

lemma ALGEBRA_CANON_CASES_THM: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((algebra_canon::bool list list => bool) l)
      ((op |::bool => bool => bool)
        ((op =::bool list list => bool list list => bool) l
          ([]::bool list list))
        ((op |::bool => bool => bool)
          ((op =::bool list list => bool list list => bool) l
            ((op #::bool list => bool list list => bool list list)
              ([]::bool list) ([]::bool list list)))
          ((Ex::(bool list list => bool) => bool)
            (%l1::bool list list.
                (Ex::(bool list list => bool) => bool)
                 (%l2::bool list list.
                     (op &::bool => bool => bool)
                      ((algebra_canon::bool list list => bool) l1)
                      ((op &::bool => bool => bool)
                        ((algebra_canon::bool list list => bool) l2)
                        ((op =::bool list list => bool list list => bool) l
                          ((op @::bool list list
                                  => bool list list => bool list list)
                            ((map::(bool list => bool list)
                                   => bool list list => bool list list)
                              ((op #::bool => bool list => bool list)
                                (True::bool))
                              l1)
                            ((map::(bool list => bool list)
                                   => bool list list => bool list list)
                              ((op #::bool => bool list => bool list)
                                (False::bool))
                              l2))))))))))"
  by (import prob_canon ALGEBRA_CANON_CASES_THM)

lemma ALGEBRA_CANON_CASES: "(All::((bool list list => bool) => bool) => bool)
 (%P::bool list list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) (P ([]::bool list list))
        ((op &::bool => bool => bool)
          (P ((op #::bool list => bool list list => bool list list)
               ([]::bool list) ([]::bool list list)))
          ((All::(bool list list => bool) => bool)
            (%l1::bool list list.
                (All::(bool list list => bool) => bool)
                 (%l2::bool list list.
                     (op -->::bool => bool => bool)
                      ((op &::bool => bool => bool)
                        ((algebra_canon::bool list list => bool) l1)
                        ((op &::bool => bool => bool)
                          ((algebra_canon::bool list list => bool) l2)
                          ((algebra_canon::bool list list => bool)
                            ((op @::bool list list
                                    => bool list list => bool list list)
                              ((map::(bool list => bool list)
                                     => bool list list => bool list list)
                                ((op #::bool => bool list => bool list)
                                  (True::bool))
                                l1)
                              ((map::(bool list => bool list)
                                     => bool list list => bool list list)
                                ((op #::bool => bool list => bool list)
                                  (False::bool))
                                l2)))))
                      (P ((op @::bool list list
                                 => bool list list => bool list list)
                           ((map::(bool list => bool list)
                                  => bool list list => bool list list)
                             ((op #::bool => bool list => bool list)
                               (True::bool))
                             l1)
                           ((map::(bool list => bool list)
                                  => bool list list => bool list list)
                             ((op #::bool => bool list => bool list)
                               (False::bool))
                             l2))))))))
      ((All::(bool list list => bool) => bool)
        (%l::bool list list.
            (op -->::bool => bool => bool)
             ((algebra_canon::bool list list => bool) l) (P l))))"
  by (import prob_canon ALGEBRA_CANON_CASES)

lemma ALGEBRA_CANON_INDUCTION: "(All::((bool list list => bool) => bool) => bool)
 (%P::bool list list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) (P ([]::bool list list))
        ((op &::bool => bool => bool)
          (P ((op #::bool list => bool list list => bool list list)
               ([]::bool list) ([]::bool list list)))
          ((All::(bool list list => bool) => bool)
            (%l1::bool list list.
                (All::(bool list list => bool) => bool)
                 (%l2::bool list list.
                     (op -->::bool => bool => bool)
                      ((op &::bool => bool => bool)
                        ((algebra_canon::bool list list => bool) l1)
                        ((op &::bool => bool => bool)
                          ((algebra_canon::bool list list => bool) l2)
                          ((op &::bool => bool => bool) (P l1)
                            ((op &::bool => bool => bool) (P l2)
                              ((algebra_canon::bool list list => bool)
                                ((op @::bool list list
  => bool list list => bool list list)
                                  ((map::(bool list => bool list)
   => bool list list => bool list list)
                                    ((op #::bool => bool list => bool list)
(True::bool))
                                    l1)
                                  ((map::(bool list => bool list)
   => bool list list => bool list list)
                                    ((op #::bool => bool list => bool list)
(False::bool))
                                    l2)))))))
                      (P ((op @::bool list list
                                 => bool list list => bool list list)
                           ((map::(bool list => bool list)
                                  => bool list list => bool list list)
                             ((op #::bool => bool list => bool list)
                               (True::bool))
                             l1)
                           ((map::(bool list => bool list)
                                  => bool list list => bool list list)
                             ((op #::bool => bool list => bool list)
                               (False::bool))
                             l2))))))))
      ((All::(bool list list => bool) => bool)
        (%l::bool list list.
            (op -->::bool => bool => bool)
             ((algebra_canon::bool list list => bool) l) (P l))))"
  by (import prob_canon ALGEBRA_CANON_INDUCTION)

lemma MEM_NIL_STEP: "ALL l1 l2. ~ [] mem map (op # True) l1 @ map (op # False) l2"
  by (import prob_canon MEM_NIL_STEP)

lemma ALG_SORTED_PREFIXFREE_MEM_NIL: "ALL l. (alg_sorted l & alg_prefixfree l & [] mem l) = (l = [[]])"
  by (import prob_canon ALG_SORTED_PREFIXFREE_MEM_NIL)

lemma ALG_SORTED_PREFIXFREE_EQUALITY: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (All::(bool list list => bool) => bool)
      (%l'::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((All::(bool list => bool) => bool)
               (%x::bool list.
                   (op =::bool => bool => bool)
                    ((op mem::bool list => bool list list => bool) x l)
                    ((op mem::bool list => bool list list => bool) x l')))
             ((op &::bool => bool => bool)
               ((alg_sorted::bool list list => bool) l)
               ((op &::bool => bool => bool)
                 ((alg_sorted::bool list list => bool) l')
                 ((op &::bool => bool => bool)
                   ((alg_prefixfree::bool list list => bool) l)
                   ((alg_prefixfree::bool list list => bool) l')))))
           ((op =::bool list list => bool list list => bool) l l')))"
  by (import prob_canon ALG_SORTED_PREFIXFREE_EQUALITY)

;end_setup

;setup_theory boolean_sequence

consts
  SHD :: "(nat => bool) => bool" 

defs
  SHD_primdef: "SHD == %f. f 0"

lemma SHD_def: "ALL f. SHD f = f 0"
  by (import boolean_sequence SHD_def)

consts
  STL :: "(nat => bool) => nat => bool" 

defs
  STL_primdef: "STL == %f n. f (Suc n)"

lemma STL_def: "ALL f n. STL f n = f (Suc n)"
  by (import boolean_sequence STL_def)

consts
  SCONS :: "bool => (nat => bool) => nat => bool" 

specification (SCONS_primdef: SCONS) SCONS_def: "(ALL h t. SCONS h t 0 = h) & (ALL h t n. SCONS h t (Suc n) = t n)"
  by (import boolean_sequence SCONS_def)

consts
  SDEST :: "(nat => bool) => bool * (nat => bool)" 

defs
  SDEST_primdef: "SDEST == %s. (SHD s, STL s)"

lemma SDEST_def: "SDEST = (%s. (SHD s, STL s))"
  by (import boolean_sequence SDEST_def)

consts
  SCONST :: "bool => nat => bool" 

defs
  SCONST_primdef: "SCONST == K"

lemma SCONST_def: "SCONST = K"
  by (import boolean_sequence SCONST_def)

consts
  STAKE :: "nat => (nat => bool) => bool list" 

specification (STAKE_primdef: STAKE) STAKE_def: "(ALL s. STAKE 0 s = []) &
(ALL n s. STAKE (Suc n) s = SHD s # STAKE n (STL s))"
  by (import boolean_sequence STAKE_def)

consts
  SDROP :: "nat => (nat => bool) => nat => bool" 

specification (SDROP_primdef: SDROP) SDROP_def: "SDROP 0 = I & (ALL n. SDROP (Suc n) = SDROP n o STL)"
  by (import boolean_sequence SDROP_def)

lemma SCONS_SURJ: "ALL x. EX xa t. x = SCONS xa t"
  by (import boolean_sequence SCONS_SURJ)

lemma SHD_STL_ISO: "ALL h t. EX x. SHD x = h & STL x = t"
  by (import boolean_sequence SHD_STL_ISO)

lemma SHD_SCONS: "ALL h t. SHD (SCONS h t) = h"
  by (import boolean_sequence SHD_SCONS)

lemma STL_SCONS: "ALL h t. STL (SCONS h t) = t"
  by (import boolean_sequence STL_SCONS)

lemma SHD_SCONST: "ALL b. SHD (SCONST b) = b"
  by (import boolean_sequence SHD_SCONST)

lemma STL_SCONST: "ALL b. STL (SCONST b) = SCONST b"
  by (import boolean_sequence STL_SCONST)

;end_setup

;setup_theory prob_algebra

consts
  alg_embed :: "bool list => (nat => bool) => bool" 

specification (alg_embed_primdef: alg_embed) alg_embed_def: "(ALL s. alg_embed [] s = True) &
(ALL h t s. alg_embed (h # t) s = (h = SHD s & alg_embed t (STL s)))"
  by (import prob_algebra alg_embed_def)

consts
  algebra_embed :: "bool list list => (nat => bool) => bool" 

specification (algebra_embed_primdef: algebra_embed) algebra_embed_def: "algebra_embed [] = EMPTY &
(ALL h t.
    algebra_embed (h # t) = pred_set.UNION (alg_embed h) (algebra_embed t))"
  by (import prob_algebra algebra_embed_def)

consts
  measurable :: "((nat => bool) => bool) => bool" 

defs
  measurable_primdef: "measurable == %s. EX b. s = algebra_embed b"

lemma measurable_def: "ALL s. measurable s = (EX b. s = algebra_embed b)"
  by (import prob_algebra measurable_def)

lemma HALVES_INTER: "pred_set.INTER (%x. SHD x = True) (%x. SHD x = False) = EMPTY"
  by (import prob_algebra HALVES_INTER)

lemma INTER_STL: "ALL p q. pred_set.INTER p q o STL = pred_set.INTER (p o STL) (q o STL)"
  by (import prob_algebra INTER_STL)

lemma COMPL_SHD: "ALL b. COMPL (%x. SHD x = b) = (%x. SHD x = (~ b))"
  by (import prob_algebra COMPL_SHD)

lemma ALG_EMBED_BASIC: "alg_embed [] = pred_set.UNIV &
(ALL h t.
    alg_embed (h # t) = pred_set.INTER (%x. SHD x = h) (alg_embed t o STL))"
  by (import prob_algebra ALG_EMBED_BASIC)

lemma ALG_EMBED_NIL: "ALL c. All (alg_embed c) = (c = [])"
  by (import prob_algebra ALG_EMBED_NIL)

lemma ALG_EMBED_POPULATED: "ALL b. Ex (alg_embed b)"
  by (import prob_algebra ALG_EMBED_POPULATED)

lemma ALG_EMBED_PREFIX: "(All::(bool list => bool) => bool)
 (%b::bool list.
     (All::(bool list => bool) => bool)
      (%c::bool list.
          (All::((nat => bool) => bool) => bool)
           (%s::nat => bool.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((alg_embed::bool list => (nat => bool) => bool) b s)
                  ((alg_embed::bool list => (nat => bool) => bool) c s))
                ((op |::bool => bool => bool)
                  ((IS_PREFIX::bool list => bool list => bool) b c)
                  ((IS_PREFIX::bool list => bool list => bool) c b)))))"
  by (import prob_algebra ALG_EMBED_PREFIX)

lemma ALG_EMBED_PREFIX_SUBSET: "ALL b c. SUBSET (alg_embed b) (alg_embed c) = IS_PREFIX b c"
  by (import prob_algebra ALG_EMBED_PREFIX_SUBSET)

lemma ALG_EMBED_TWINS: "ALL l.
   pred_set.UNION (alg_embed (SNOC True l)) (alg_embed (SNOC False l)) =
   alg_embed l"
  by (import prob_algebra ALG_EMBED_TWINS)

lemma ALGEBRA_EMBED_BASIC: "algebra_embed [] = EMPTY &
algebra_embed [[]] = pred_set.UNIV &
(ALL b. algebra_embed [[b]] = (%s. SHD s = b))"
  by (import prob_algebra ALGEBRA_EMBED_BASIC)

lemma ALGEBRA_EMBED_MEM: "(All::(bool list list => bool) => bool)
 (%b::bool list list.
     (All::((nat => bool) => bool) => bool)
      (%x::nat => bool.
          (op -->::bool => bool => bool)
           ((algebra_embed::bool list list => (nat => bool) => bool) b x)
           ((Ex::(bool list => bool) => bool)
             (%l::bool list.
                 (op &::bool => bool => bool)
                  ((op mem::bool list => bool list list => bool) l b)
                  ((alg_embed::bool list => (nat => bool) => bool) l x)))))"
  by (import prob_algebra ALGEBRA_EMBED_MEM)

lemma ALGEBRA_EMBED_APPEND: "ALL l1 l2.
   algebra_embed (l1 @ l2) =
   pred_set.UNION (algebra_embed l1) (algebra_embed l2)"
  by (import prob_algebra ALGEBRA_EMBED_APPEND)

lemma ALGEBRA_EMBED_TLS: "ALL l b.
   algebra_embed (map (op # b) l) (SCONS h t) = (h = b & algebra_embed l t)"
  by (import prob_algebra ALGEBRA_EMBED_TLS)

lemma ALG_CANON_PREFS_EMBED: "ALL l b. algebra_embed (alg_canon_prefs l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_PREFS_EMBED)

lemma ALG_CANON_FIND_EMBED: "ALL l b. algebra_embed (alg_canon_find l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_FIND_EMBED)

lemma ALG_CANON1_EMBED: "ALL x. algebra_embed (alg_canon1 x) = algebra_embed x"
  by (import prob_algebra ALG_CANON1_EMBED)

lemma ALG_CANON_MERGE_EMBED: "ALL l b. algebra_embed (alg_canon_merge l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_MERGE_EMBED)

lemma ALG_CANON2_EMBED: "ALL x. algebra_embed (alg_canon2 x) = algebra_embed x"
  by (import prob_algebra ALG_CANON2_EMBED)

lemma ALG_CANON_EMBED: "ALL l. algebra_embed (alg_canon l) = algebra_embed l"
  by (import prob_algebra ALG_CANON_EMBED)

lemma ALGEBRA_CANON_UNIV: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((algebra_canon::bool list list => bool) l)
      ((op -->::bool => bool => bool)
        ((op =::((nat => bool) => bool) => ((nat => bool) => bool) => bool)
          ((algebra_embed::bool list list => (nat => bool) => bool) l)
          (pred_set.UNIV::(nat => bool) => bool))
        ((op =::bool list list => bool list list => bool) l
          ((op #::bool list => bool list list => bool list list)
            ([]::bool list) ([]::bool list list)))))"
  by (import prob_algebra ALGEBRA_CANON_UNIV)

lemma ALG_CANON_REP: "ALL b c. (alg_canon b = alg_canon c) = (algebra_embed b = algebra_embed c)"
  by (import prob_algebra ALG_CANON_REP)

lemma ALGEBRA_CANON_EMBED_EMPTY: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((algebra_canon::bool list list => bool) l)
      ((op =::bool => bool => bool)
        ((All::((nat => bool) => bool) => bool)
          (%v::nat => bool.
              (Not::bool => bool)
               ((algebra_embed::bool list list => (nat => bool) => bool) l
                 v)))
        ((op =::bool list list => bool list list => bool) l
          ([]::bool list list))))"
  by (import prob_algebra ALGEBRA_CANON_EMBED_EMPTY)

lemma ALGEBRA_CANON_EMBED_UNIV: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((algebra_canon::bool list list => bool) l)
      ((op =::bool => bool => bool)
        ((All::((nat => bool) => bool) => bool)
          ((algebra_embed::bool list list => (nat => bool) => bool) l))
        ((op =::bool list list => bool list list => bool) l
          ((op #::bool list => bool list list => bool list list)
            ([]::bool list) ([]::bool list list)))))"
  by (import prob_algebra ALGEBRA_CANON_EMBED_UNIV)

lemma MEASURABLE_ALGEBRA: "ALL b. measurable (algebra_embed b)"
  by (import prob_algebra MEASURABLE_ALGEBRA)

lemma MEASURABLE_BASIC: "measurable EMPTY &
measurable pred_set.UNIV & (ALL b. measurable (%s. SHD s = b))"
  by (import prob_algebra MEASURABLE_BASIC)

lemma MEASURABLE_SHD: "ALL b. measurable (%s. SHD s = b)"
  by (import prob_algebra MEASURABLE_SHD)

lemma ALGEBRA_EMBED_COMPL: "ALL l. EX l'. COMPL (algebra_embed l) = algebra_embed l'"
  by (import prob_algebra ALGEBRA_EMBED_COMPL)

lemma MEASURABLE_COMPL: "ALL s. measurable (COMPL s) = measurable s"
  by (import prob_algebra MEASURABLE_COMPL)

lemma MEASURABLE_UNION: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (All::(((nat => bool) => bool) => bool) => bool)
      (%t::(nat => bool) => bool.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((measurable::((nat => bool) => bool) => bool) s)
             ((measurable::((nat => bool) => bool) => bool) t))
           ((measurable::((nat => bool) => bool) => bool)
             ((pred_set.UNION::((nat => bool) => bool)
                               => ((nat => bool) => bool)
                                  => (nat => bool) => bool)
               s t))))"
  by (import prob_algebra MEASURABLE_UNION)

lemma MEASURABLE_INTER: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (All::(((nat => bool) => bool) => bool) => bool)
      (%t::(nat => bool) => bool.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((measurable::((nat => bool) => bool) => bool) s)
             ((measurable::((nat => bool) => bool) => bool) t))
           ((measurable::((nat => bool) => bool) => bool)
             ((pred_set.INTER::((nat => bool) => bool)
                               => ((nat => bool) => bool)
                                  => (nat => bool) => bool)
               s t))))"
  by (import prob_algebra MEASURABLE_INTER)

lemma MEASURABLE_STL: "ALL p. measurable (p o STL) = measurable p"
  by (import prob_algebra MEASURABLE_STL)

lemma MEASURABLE_SDROP: "ALL n p. measurable (p o SDROP n) = measurable p"
  by (import prob_algebra MEASURABLE_SDROP)

lemma MEASURABLE_INTER_HALVES: "ALL p.
   (measurable (pred_set.INTER (%x. SHD x = True) p) &
    measurable (pred_set.INTER (%x. SHD x = False) p)) =
   measurable p"
  by (import prob_algebra MEASURABLE_INTER_HALVES)

lemma MEASURABLE_HALVES: "ALL p q.
   measurable
    (pred_set.UNION (pred_set.INTER (%x. SHD x = True) p)
      (pred_set.INTER (%x. SHD x = False) q)) =
   (measurable (pred_set.INTER (%x. SHD x = True) p) &
    measurable (pred_set.INTER (%x. SHD x = False) q))"
  by (import prob_algebra MEASURABLE_HALVES)

lemma MEASURABLE_INTER_SHD: "ALL b p.
   measurable (pred_set.INTER (%x. SHD x = b) (p o STL)) = measurable p"
  by (import prob_algebra MEASURABLE_INTER_SHD)

;end_setup

;setup_theory prob

consts
  alg_measure :: "bool list list => real" 

specification (alg_measure_primdef: alg_measure) alg_measure_def: "alg_measure [] = 0 &
(ALL l rest. alg_measure (l # rest) = (1 / 2) ^ length l + alg_measure rest)"
  by (import prob alg_measure_def)

consts
  algebra_measure :: "bool list list => real" 

defs
  algebra_measure_primdef: "algebra_measure ==
%b. inf (%r. EX c. algebra_embed b = algebra_embed c & alg_measure c = r)"

lemma algebra_measure_def: "ALL b.
   algebra_measure b =
   inf (%r. EX c. algebra_embed b = algebra_embed c & alg_measure c = r)"
  by (import prob algebra_measure_def)

consts
  prob :: "((nat => bool) => bool) => real" 

defs
  prob_primdef: "prob ==
%s. sup (%r. EX b. algebra_measure b = r & SUBSET (algebra_embed b) s)"

lemma prob_def: "ALL s.
   prob s =
   sup (%r. EX b. algebra_measure b = r & SUBSET (algebra_embed b) s)"
  by (import prob prob_def)

lemma ALG_TWINS_MEASURE: "ALL l::bool list.
   ((1::real) / (2::real)) ^ length (SNOC True l) +
   ((1::real) / (2::real)) ^ length (SNOC False l) =
   ((1::real) / (2::real)) ^ length l"
  by (import prob ALG_TWINS_MEASURE)

lemma ALG_MEASURE_BASIC: "alg_measure [] = 0 &
alg_measure [[]] = 1 & (ALL b. alg_measure [[b]] = 1 / 2)"
  by (import prob ALG_MEASURE_BASIC)

lemma ALG_MEASURE_POS: "ALL l. 0 <= alg_measure l"
  by (import prob ALG_MEASURE_POS)

lemma ALG_MEASURE_APPEND: "ALL l1 l2. alg_measure (l1 @ l2) = alg_measure l1 + alg_measure l2"
  by (import prob ALG_MEASURE_APPEND)

lemma ALG_MEASURE_TLS: "ALL l b. 2 * alg_measure (map (op # b) l) = alg_measure l"
  by (import prob ALG_MEASURE_TLS)

lemma ALG_CANON_PREFS_MONO: "ALL l b. alg_measure (alg_canon_prefs l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_PREFS_MONO)

lemma ALG_CANON_FIND_MONO: "ALL l b. alg_measure (alg_canon_find l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_FIND_MONO)

lemma ALG_CANON1_MONO: "ALL x. alg_measure (alg_canon1 x) <= alg_measure x"
  by (import prob ALG_CANON1_MONO)

lemma ALG_CANON_MERGE_MONO: "ALL l b. alg_measure (alg_canon_merge l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_MERGE_MONO)

lemma ALG_CANON2_MONO: "ALL x. alg_measure (alg_canon2 x) <= alg_measure x"
  by (import prob ALG_CANON2_MONO)

lemma ALG_CANON_MONO: "ALL l. alg_measure (alg_canon l) <= alg_measure l"
  by (import prob ALG_CANON_MONO)

lemma ALGEBRA_MEASURE_DEF_ALT: "ALL l. algebra_measure l = alg_measure (alg_canon l)"
  by (import prob ALGEBRA_MEASURE_DEF_ALT)

lemma ALGEBRA_MEASURE_BASIC: "algebra_measure [] = 0 &
algebra_measure [[]] = 1 & (ALL b. algebra_measure [[b]] = 1 / 2)"
  by (import prob ALGEBRA_MEASURE_BASIC)

lemma ALGEBRA_CANON_MEASURE_MAX: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((algebra_canon::bool list list => bool) l)
      ((op <=::real => real => bool)
        ((alg_measure::bool list list => real) l) (1::real)))"
  by (import prob ALGEBRA_CANON_MEASURE_MAX)

lemma ALGEBRA_MEASURE_MAX: "ALL l. algebra_measure l <= 1"
  by (import prob ALGEBRA_MEASURE_MAX)

lemma ALGEBRA_MEASURE_MONO_EMBED: "(All::(bool list list => bool) => bool)
 (%x::bool list list.
     (All::(bool list list => bool) => bool)
      (%xa::bool list list.
          (op -->::bool => bool => bool)
           ((SUBSET::((nat => bool) => bool)
                     => ((nat => bool) => bool) => bool)
             ((algebra_embed::bool list list => (nat => bool) => bool) x)
             ((algebra_embed::bool list list => (nat => bool) => bool) xa))
           ((op <=::real => real => bool)
             ((algebra_measure::bool list list => real) x)
             ((algebra_measure::bool list list => real) xa))))"
  by (import prob ALGEBRA_MEASURE_MONO_EMBED)

lemma ALG_MEASURE_COMPL: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((algebra_canon::bool list list => bool) l)
      ((All::(bool list list => bool) => bool)
        (%c::bool list list.
            (op -->::bool => bool => bool)
             ((algebra_canon::bool list list => bool) c)
             ((op -->::bool => bool => bool)
               ((op =::((nat => bool) => bool)
                       => ((nat => bool) => bool) => bool)
                 ((COMPL::((nat => bool) => bool) => (nat => bool) => bool)
                   ((algebra_embed::bool list list => (nat => bool) => bool)
                     l))
                 ((algebra_embed::bool list list => (nat => bool) => bool)
                   c))
               ((op =::real => real => bool)
                 ((op +::real => real => real)
                   ((alg_measure::bool list list => real) l)
                   ((alg_measure::bool list list => real) c))
                 (1::real))))))"
  by (import prob ALG_MEASURE_COMPL)

lemma ALG_MEASURE_ADDITIVE: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((algebra_canon::bool list list => bool) l)
      ((All::(bool list list => bool) => bool)
        (%c::bool list list.
            (op -->::bool => bool => bool)
             ((algebra_canon::bool list list => bool) c)
             ((All::(bool list list => bool) => bool)
               (%d::bool list list.
                   (op -->::bool => bool => bool)
                    ((algebra_canon::bool list list => bool) d)
                    ((op -->::bool => bool => bool)
                      ((op &::bool => bool => bool)
                        ((op =::((nat => bool) => bool)
                                => ((nat => bool) => bool) => bool)
                          ((pred_set.INTER::((nat => bool) => bool)
      => ((nat => bool) => bool) => (nat => bool) => bool)
                            ((algebra_embed::bool list list
       => (nat => bool) => bool)
                              c)
                            ((algebra_embed::bool list list
       => (nat => bool) => bool)
                              d))
                          (EMPTY::(nat => bool) => bool))
                        ((op =::((nat => bool) => bool)
                                => ((nat => bool) => bool) => bool)
                          ((algebra_embed::bool list list
     => (nat => bool) => bool)
                            l)
                          ((pred_set.UNION::((nat => bool) => bool)
      => ((nat => bool) => bool) => (nat => bool) => bool)
                            ((algebra_embed::bool list list
       => (nat => bool) => bool)
                              c)
                            ((algebra_embed::bool list list
       => (nat => bool) => bool)
                              d))))
                      ((op =::real => real => bool)
                        ((alg_measure::bool list list => real) l)
                        ((op +::real => real => real)
                          ((alg_measure::bool list list => real) c)
                          ((alg_measure::bool list list => real) d)))))))))"
  by (import prob ALG_MEASURE_ADDITIVE)

lemma PROB_ALGEBRA: "ALL l. prob (algebra_embed l) = algebra_measure l"
  by (import prob PROB_ALGEBRA)

lemma PROB_BASIC: "prob EMPTY = 0 &
prob pred_set.UNIV = 1 & (ALL b. prob (%s. SHD s = b) = 1 / 2)"
  by (import prob PROB_BASIC)

lemma PROB_ADDITIVE: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (All::(((nat => bool) => bool) => bool) => bool)
      (%t::(nat => bool) => bool.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((measurable::((nat => bool) => bool) => bool) s)
             ((op &::bool => bool => bool)
               ((measurable::((nat => bool) => bool) => bool) t)
               ((op =::((nat => bool) => bool)
                       => ((nat => bool) => bool) => bool)
                 ((pred_set.INTER::((nat => bool) => bool)
                                   => ((nat => bool) => bool)
=> (nat => bool) => bool)
                   s t)
                 (EMPTY::(nat => bool) => bool))))
           ((op =::real => real => bool)
             ((prob::((nat => bool) => bool) => real)
               ((pred_set.UNION::((nat => bool) => bool)
                                 => ((nat => bool) => bool)
                                    => (nat => bool) => bool)
                 s t))
             ((op +::real => real => real)
               ((prob::((nat => bool) => bool) => real) s)
               ((prob::((nat => bool) => bool) => real) t)))))"
  by (import prob PROB_ADDITIVE)

lemma PROB_COMPL: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (op -->::bool => bool => bool)
      ((measurable::((nat => bool) => bool) => bool) s)
      ((op =::real => real => bool)
        ((prob::((nat => bool) => bool) => real)
          ((COMPL::((nat => bool) => bool) => (nat => bool) => bool) s))
        ((op -::real => real => real) (1::real)
          ((prob::((nat => bool) => bool) => real) s))))"
  by (import prob PROB_COMPL)

lemma PROB_SUP_EXISTS1: "ALL s. EX x b. algebra_measure b = x & SUBSET (algebra_embed b) s"
  by (import prob PROB_SUP_EXISTS1)

lemma PROB_SUP_EXISTS2: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (Ex::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%r::real.
               (op -->::bool => bool => bool)
                ((Ex::(bool list list => bool) => bool)
                  (%b::bool list list.
                      (op &::bool => bool => bool)
                       ((op =::real => real => bool)
                         ((algebra_measure::bool list list => real) b) r)
                       ((SUBSET::((nat => bool) => bool)
                                 => ((nat => bool) => bool) => bool)
                         ((algebra_embed::bool list list
    => (nat => bool) => bool)
                           b)
                         s)))
                ((op <=::real => real => bool) r x))))"
  by (import prob PROB_SUP_EXISTS2)

lemma PROB_LE_X: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((All::(((nat => bool) => bool) => bool) => bool)
             (%s'::(nat => bool) => bool.
                 (op -->::bool => bool => bool)
                  ((op &::bool => bool => bool)
                    ((measurable::((nat => bool) => bool) => bool) s')
                    ((SUBSET::((nat => bool) => bool)
                              => ((nat => bool) => bool) => bool)
                      s' s))
                  ((op <=::real => real => bool)
                    ((prob::((nat => bool) => bool) => real) s') x)))
           ((op <=::real => real => bool)
             ((prob::((nat => bool) => bool) => real) s) x)))"
  by (import prob PROB_LE_X)

lemma X_LE_PROB: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((Ex::(((nat => bool) => bool) => bool) => bool)
             (%s'::(nat => bool) => bool.
                 (op &::bool => bool => bool)
                  ((measurable::((nat => bool) => bool) => bool) s')
                  ((op &::bool => bool => bool)
                    ((SUBSET::((nat => bool) => bool)
                              => ((nat => bool) => bool) => bool)
                      s' s)
                    ((op <=::real => real => bool) x
                      ((prob::((nat => bool) => bool) => real) s')))))
           ((op <=::real => real => bool) x
             ((prob::((nat => bool) => bool) => real) s))))"
  by (import prob X_LE_PROB)

lemma PROB_SUBSET_MONO: "(All::(((nat => bool) => bool) => bool) => bool)
 (%s::(nat => bool) => bool.
     (All::(((nat => bool) => bool) => bool) => bool)
      (%t::(nat => bool) => bool.
          (op -->::bool => bool => bool)
           ((SUBSET::((nat => bool) => bool)
                     => ((nat => bool) => bool) => bool)
             s t)
           ((op <=::real => real => bool)
             ((prob::((nat => bool) => bool) => real) s)
             ((prob::((nat => bool) => bool) => real) t))))"
  by (import prob PROB_SUBSET_MONO)

lemma PROB_ALG: "ALL x. prob (alg_embed x) = (1 / 2) ^ length x"
  by (import prob PROB_ALG)

lemma PROB_STL: "(All::(((nat => bool) => bool) => bool) => bool)
 (%p::(nat => bool) => bool.
     (op -->::bool => bool => bool)
      ((measurable::((nat => bool) => bool) => bool) p)
      ((op =::real => real => bool)
        ((prob::((nat => bool) => bool) => real)
          ((op o::((nat => bool) => bool)
                  => ((nat => bool) => nat => bool)
                     => (nat => bool) => bool)
            p (STL::(nat => bool) => nat => bool)))
        ((prob::((nat => bool) => bool) => real) p)))"
  by (import prob PROB_STL)

lemma PROB_SDROP: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(((nat => bool) => bool) => bool) => bool)
      (%p::(nat => bool) => bool.
          (op -->::bool => bool => bool)
           ((measurable::((nat => bool) => bool) => bool) p)
           ((op =::real => real => bool)
             ((prob::((nat => bool) => bool) => real)
               ((op o::((nat => bool) => bool)
                       => ((nat => bool) => nat => bool)
                          => (nat => bool) => bool)
                 p ((SDROP::nat => (nat => bool) => nat => bool) n)))
             ((prob::((nat => bool) => bool) => real) p))))"
  by (import prob PROB_SDROP)

lemma PROB_INTER_HALVES: "(All::(((nat => bool) => bool) => bool) => bool)
 (%p::(nat => bool) => bool.
     (op -->::bool => bool => bool)
      ((measurable::((nat => bool) => bool) => bool) p)
      ((op =::real => real => bool)
        ((op +::real => real => real)
          ((prob::((nat => bool) => bool) => real)
            ((pred_set.INTER::((nat => bool) => bool)
                              => ((nat => bool) => bool)
                                 => (nat => bool) => bool)
              (%x::nat => bool.
                  (op =::bool => bool => bool)
                   ((SHD::(nat => bool) => bool) x) (True::bool))
              p))
          ((prob::((nat => bool) => bool) => real)
            ((pred_set.INTER::((nat => bool) => bool)
                              => ((nat => bool) => bool)
                                 => (nat => bool) => bool)
              (%x::nat => bool.
                  (op =::bool => bool => bool)
                   ((SHD::(nat => bool) => bool) x) (False::bool))
              p)))
        ((prob::((nat => bool) => bool) => real) p)))"
  by (import prob PROB_INTER_HALVES)

lemma PROB_INTER_SHD: "(All::(bool => bool) => bool)
 (%b::bool.
     (All::(((nat => bool) => bool) => bool) => bool)
      (%p::(nat => bool) => bool.
          (op -->::bool => bool => bool)
           ((measurable::((nat => bool) => bool) => bool) p)
           ((op =::real => real => bool)
             ((prob::((nat => bool) => bool) => real)
               ((pred_set.INTER::((nat => bool) => bool)
                                 => ((nat => bool) => bool)
                                    => (nat => bool) => bool)
                 (%x::nat => bool.
                     (op =::bool => bool => bool)
                      ((SHD::(nat => bool) => bool) x) b)
                 ((op o::((nat => bool) => bool)
                         => ((nat => bool) => nat => bool)
                            => (nat => bool) => bool)
                   p (STL::(nat => bool) => nat => bool))))
             ((op *::real => real => real)
               ((op /::real => real => real) (1::real)
                 ((number_of::bin => real)
                   ((op BIT::bin => bool => bin)
                     ((op BIT::bin => bool => bin) (bin.Pls::bin)
                       (True::bool))
                     (False::bool))))
               ((prob::((nat => bool) => bool) => real) p)))))"
  by (import prob PROB_INTER_SHD)

lemma ALGEBRA_MEASURE_POS: "ALL l. 0 <= algebra_measure l"
  by (import prob ALGEBRA_MEASURE_POS)

lemma ALGEBRA_MEASURE_RANGE: "ALL l. 0 <= algebra_measure l & algebra_measure l <= 1"
  by (import prob ALGEBRA_MEASURE_RANGE)

lemma PROB_POS: "ALL p. 0 <= prob p"
  by (import prob PROB_POS)

lemma PROB_MAX: "ALL p. prob p <= 1"
  by (import prob PROB_MAX)

lemma PROB_RANGE: "ALL p. 0 <= prob p & prob p <= 1"
  by (import prob PROB_RANGE)

lemma ABS_PROB: "ALL p. abs (prob p) = prob p"
  by (import prob ABS_PROB)

lemma PROB_SHD: "ALL b. prob (%s. SHD s = b) = 1 / 2"
  by (import prob PROB_SHD)

lemma PROB_COMPL_LE1: "(All::(((nat => bool) => bool) => bool) => bool)
 (%p::(nat => bool) => bool.
     (All::(real => bool) => bool)
      (%r::real.
          (op -->::bool => bool => bool)
           ((measurable::((nat => bool) => bool) => bool) p)
           ((op =::bool => bool => bool)
             ((op <=::real => real => bool)
               ((prob::((nat => bool) => bool) => real)
                 ((COMPL::((nat => bool) => bool) => (nat => bool) => bool)
                   p))
               r)
             ((op <=::real => real => bool)
               ((op -::real => real => real) (1::real) r)
               ((prob::((nat => bool) => bool) => real) p)))))"
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
  pseudo_linear_tl_primdef: "pseudo_linear_tl == %a b n x. (a * x + b) mod (2 * n + 1)"

lemma pseudo_linear_tl_def: "ALL a b n x. pseudo_linear_tl a b n x = (a * x + b) mod (2 * n + 1)"
  by (import prob_pseudo pseudo_linear_tl_def)

lemma PSEUDO_LINEAR1_EXECUTE: "EX x. (ALL xa. SHD (x xa) = pseudo_linear_hd xa) &
      (ALL xa.
          STL (x xa) =
          x (pseudo_linear_tl
              (NUMERAL
                (NUMERAL_BIT1
                  (NUMERAL_BIT1
                    (NUMERAL_BIT1
                      (NUMERAL_BIT2
                        (NUMERAL_BIT1 (NUMERAL_BIT2 ALT_ZERO)))))))
              (NUMERAL
                (NUMERAL_BIT1
                  (NUMERAL_BIT1
                    (NUMERAL_BIT1
                      (NUMERAL_BIT1
                        (NUMERAL_BIT1 (NUMERAL_BIT2 ALT_ZERO)))))))
              (NUMERAL
                (NUMERAL_BIT1
                  (NUMERAL_BIT1
                    (NUMERAL_BIT1
                      (NUMERAL_BIT1
                        (NUMERAL_BIT2 (NUMERAL_BIT1 ALT_ZERO)))))))
              xa))"
  by (import prob_pseudo PSEUDO_LINEAR1_EXECUTE)

consts
  pseudo_linear1 :: "nat => nat => bool" 

specification (pseudo_linear1_primdef: pseudo_linear1) pseudo_linear1_def: "(ALL x. SHD (pseudo_linear1 x) = pseudo_linear_hd x) &
(ALL x.
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
%p q. measurable p &
      measurable q & prob (pred_set.INTER p q) = prob p * prob q"

lemma indep_set_def: "ALL p q.
   indep_set p q =
   (measurable p &
    measurable q & prob (pred_set.INTER p q) = prob p * prob q)"
  by (import prob_indep indep_set_def)

consts
  alg_cover_set :: "bool list list => bool" 

defs
  alg_cover_set_primdef: "alg_cover_set ==
%l. alg_sorted l & alg_prefixfree l & algebra_embed l = pred_set.UNIV"

lemma alg_cover_set_def: "ALL l.
   alg_cover_set l =
   (alg_sorted l & alg_prefixfree l & algebra_embed l = pred_set.UNIV)"
  by (import prob_indep alg_cover_set_def)

consts
  alg_cover :: "bool list list => (nat => bool) => bool list" 

defs
  alg_cover_primdef: "alg_cover == %l x. SOME b. b mem l & alg_embed b x"

lemma alg_cover_def: "ALL l x. alg_cover l x = (SOME b. b mem l & alg_embed b x)"
  by (import prob_indep alg_cover_def)

consts
  indep :: "((nat => bool) => 'a * (nat => bool)) => bool" 

defs
  indep_primdef: "indep ==
%f. EX l r.
       alg_cover_set l &
       (ALL s. f s = (let c = alg_cover l s in (r c, SDROP (length c) s)))"

lemma indep_def: "ALL f.
   indep f =
   (EX l r.
       alg_cover_set l &
       (ALL s. f s = (let c = alg_cover l s in (r c, SDROP (length c) s))))"
  by (import prob_indep indep_def)

lemma INDEP_SET_BASIC: "(All::(((nat => bool) => bool) => bool) => bool)
 (%p::(nat => bool) => bool.
     (op -->::bool => bool => bool)
      ((measurable::((nat => bool) => bool) => bool) p)
      ((op &::bool => bool => bool)
        ((indep_set::((nat => bool) => bool)
                     => ((nat => bool) => bool) => bool)
          (EMPTY::(nat => bool) => bool) p)
        ((indep_set::((nat => bool) => bool)
                     => ((nat => bool) => bool) => bool)
          (pred_set.UNIV::(nat => bool) => bool) p)))"
  by (import prob_indep INDEP_SET_BASIC)

lemma INDEP_SET_SYM: "ALL p q. indep_set p q = indep_set p q"
  by (import prob_indep INDEP_SET_SYM)

lemma INDEP_SET_DISJOINT_DECOMP: "(All::(((nat => bool) => bool) => bool) => bool)
 (%p::(nat => bool) => bool.
     (All::(((nat => bool) => bool) => bool) => bool)
      (%q::(nat => bool) => bool.
          (All::(((nat => bool) => bool) => bool) => bool)
           (%r::(nat => bool) => bool.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((indep_set::((nat => bool) => bool)
                               => ((nat => bool) => bool) => bool)
                    p r)
                  ((op &::bool => bool => bool)
                    ((indep_set::((nat => bool) => bool)
                                 => ((nat => bool) => bool) => bool)
                      q r)
                    ((op =::((nat => bool) => bool)
                            => ((nat => bool) => bool) => bool)
                      ((pred_set.INTER::((nat => bool) => bool)
  => ((nat => bool) => bool) => (nat => bool) => bool)
                        p q)
                      (EMPTY::(nat => bool) => bool))))
                ((indep_set::((nat => bool) => bool)
                             => ((nat => bool) => bool) => bool)
                  ((pred_set.UNION::((nat => bool) => bool)
                                    => ((nat => bool) => bool)
 => (nat => bool) => bool)
                    p q)
                  r))))"
  by (import prob_indep INDEP_SET_DISJOINT_DECOMP)

lemma ALG_COVER_SET_BASIC: "~ alg_cover_set [] & alg_cover_set [[]] & alg_cover_set [[True], [False]]"
  by (import prob_indep ALG_COVER_SET_BASIC)

lemma ALG_COVER_WELL_DEFINED: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (All::((nat => bool) => bool) => bool)
      (%x::nat => bool.
          (op -->::bool => bool => bool)
           ((alg_cover_set::bool list list => bool) l)
           ((op &::bool => bool => bool)
             ((op mem::bool list => bool list list => bool)
               ((alg_cover::bool list list => (nat => bool) => bool list) l
                 x)
               l)
             ((alg_embed::bool list => (nat => bool) => bool)
               ((alg_cover::bool list list => (nat => bool) => bool list) l
                 x)
               x))))"
  by (import prob_indep ALG_COVER_WELL_DEFINED)

lemma ALG_COVER_UNIV: "alg_cover [[]] = K []"
  by (import prob_indep ALG_COVER_UNIV)

lemma MAP_CONS_TL_FILTER: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (All::(bool => bool) => bool)
      (%b::bool.
          (op -->::bool => bool => bool)
           ((Not::bool => bool)
             ((op mem::bool list => bool list list => bool) ([]::bool list)
               l))
           ((op =::bool list list => bool list list => bool)
             ((map::(bool list => bool list)
                    => bool list list => bool list list)
               ((op #::bool => bool list => bool list) b)
               ((map::(bool list => bool list)
                      => bool list list => bool list list)
                 (tl::bool list => bool list)
                 ((filter::(bool list => bool)
                           => bool list list => bool list list)
                   (%x::bool list.
                       (op =::bool => bool => bool)
                        ((hd::bool list => bool) x) b)
                   l)))
             ((filter::(bool list => bool)
                       => bool list list => bool list list)
               (%x::bool list.
                   (op =::bool => bool => bool) ((hd::bool list => bool) x)
                    b)
               l))))"
  by (import prob_indep MAP_CONS_TL_FILTER)

lemma ALG_COVER_SET_CASES_THM: "ALL l.
   alg_cover_set l =
   (l = [[]] |
    (EX x xa.
        alg_cover_set x &
        alg_cover_set xa & l = map (op # True) x @ map (op # False) xa))"
  by (import prob_indep ALG_COVER_SET_CASES_THM)

lemma ALG_COVER_SET_CASES: "(All::((bool list list => bool) => bool) => bool)
 (%P::bool list list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        (P ((op #::bool list => bool list list => bool list list)
             ([]::bool list) ([]::bool list list)))
        ((All::(bool list list => bool) => bool)
          (%l1::bool list list.
              (All::(bool list list => bool) => bool)
               (%l2::bool list list.
                   (op -->::bool => bool => bool)
                    ((op &::bool => bool => bool)
                      ((alg_cover_set::bool list list => bool) l1)
                      ((op &::bool => bool => bool)
                        ((alg_cover_set::bool list list => bool) l2)
                        ((alg_cover_set::bool list list => bool)
                          ((op @::bool list list
                                  => bool list list => bool list list)
                            ((map::(bool list => bool list)
                                   => bool list list => bool list list)
                              ((op #::bool => bool list => bool list)
                                (True::bool))
                              l1)
                            ((map::(bool list => bool list)
                                   => bool list list => bool list list)
                              ((op #::bool => bool list => bool list)
                                (False::bool))
                              l2)))))
                    (P ((op @::bool list list
                               => bool list list => bool list list)
                         ((map::(bool list => bool list)
                                => bool list list => bool list list)
                           ((op #::bool => bool list => bool list)
                             (True::bool))
                           l1)
                         ((map::(bool list => bool list)
                                => bool list list => bool list list)
                           ((op #::bool => bool list => bool list)
                             (False::bool))
                           l2)))))))
      ((All::(bool list list => bool) => bool)
        (%l::bool list list.
            (op -->::bool => bool => bool)
             ((alg_cover_set::bool list list => bool) l) (P l))))"
  by (import prob_indep ALG_COVER_SET_CASES)

lemma ALG_COVER_SET_INDUCTION: "(All::((bool list list => bool) => bool) => bool)
 (%P::bool list list => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        (P ((op #::bool list => bool list list => bool list list)
             ([]::bool list) ([]::bool list list)))
        ((All::(bool list list => bool) => bool)
          (%l1::bool list list.
              (All::(bool list list => bool) => bool)
               (%l2::bool list list.
                   (op -->::bool => bool => bool)
                    ((op &::bool => bool => bool)
                      ((alg_cover_set::bool list list => bool) l1)
                      ((op &::bool => bool => bool)
                        ((alg_cover_set::bool list list => bool) l2)
                        ((op &::bool => bool => bool) (P l1)
                          ((op &::bool => bool => bool) (P l2)
                            ((alg_cover_set::bool list list => bool)
                              ((op @::bool list list
=> bool list list => bool list list)
                                ((map::(bool list => bool list)
 => bool list list => bool list list)
                                  ((op #::bool => bool list => bool list)
                                    (True::bool))
                                  l1)
                                ((map::(bool list => bool list)
 => bool list list => bool list list)
                                  ((op #::bool => bool list => bool list)
                                    (False::bool))
                                  l2)))))))
                    (P ((op @::bool list list
                               => bool list list => bool list list)
                         ((map::(bool list => bool list)
                                => bool list list => bool list list)
                           ((op #::bool => bool list => bool list)
                             (True::bool))
                           l1)
                         ((map::(bool list => bool list)
                                => bool list list => bool list list)
                           ((op #::bool => bool list => bool list)
                             (False::bool))
                           l2)))))))
      ((All::(bool list list => bool) => bool)
        (%l::bool list list.
            (op -->::bool => bool => bool)
             ((alg_cover_set::bool list list => bool) l) (P l))))"
  by (import prob_indep ALG_COVER_SET_INDUCTION)

lemma ALG_COVER_EXISTS_UNIQUE: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((alg_cover_set::bool list list => bool) l)
      ((All::((nat => bool) => bool) => bool)
        (%s::nat => bool.
            (Ex1::(bool list => bool) => bool)
             (%x::bool list.
                 (op &::bool => bool => bool)
                  ((op mem::bool list => bool list list => bool) x l)
                  ((alg_embed::bool list => (nat => bool) => bool) x s)))))"
  by (import prob_indep ALG_COVER_EXISTS_UNIQUE)

lemma ALG_COVER_UNIQUE: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (All::(bool list => bool) => bool)
      (%x::bool list.
          (All::((nat => bool) => bool) => bool)
           (%s::nat => bool.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((alg_cover_set::bool list list => bool) l)
                  ((op &::bool => bool => bool)
                    ((op mem::bool list => bool list list => bool) x l)
                    ((alg_embed::bool list => (nat => bool) => bool) x s)))
                ((op =::bool list => bool list => bool)
                  ((alg_cover::bool list list => (nat => bool) => bool list)
                    l s)
                  x))))"
  by (import prob_indep ALG_COVER_UNIQUE)

lemma ALG_COVER_STEP: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (All::(bool => bool) => bool)
           (%h::bool.
               (All::((nat => bool) => bool) => bool)
                (%t::nat => bool.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((alg_cover_set::bool list list => bool) l1)
                       ((alg_cover_set::bool list list => bool) l2))
                     ((op =::bool list => bool list => bool)
                       ((alg_cover::bool list list
                                    => (nat => bool) => bool list)
                         ((op @::bool list list
                                 => bool list list => bool list list)
                           ((map::(bool list => bool list)
                                  => bool list list => bool list list)
                             ((op #::bool => bool list => bool list)
                               (True::bool))
                             l1)
                           ((map::(bool list => bool list)
                                  => bool list list => bool list list)
                             ((op #::bool => bool list => bool list)
                               (False::bool))
                             l2))
                         ((SCONS::bool => (nat => bool) => nat => bool) h
                           t))
                       ((If::bool => bool list => bool list => bool list) h
                         ((op #::bool => bool list => bool list)
                           (True::bool)
                           ((alg_cover::bool list list
  => (nat => bool) => bool list)
                             l1 t))
                         ((op #::bool => bool list => bool list)
                           (False::bool)
                           ((alg_cover::bool list list
  => (nat => bool) => bool list)
                             l2 t))))))))"
  by (import prob_indep ALG_COVER_STEP)

lemma ALG_COVER_HEAD: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((alg_cover_set::bool list list => bool) l)
      ((All::((bool list => bool) => bool) => bool)
        (%f::bool list => bool.
            (op =::((nat => bool) => bool)
                   => ((nat => bool) => bool) => bool)
             ((op o::(bool list => bool)
                     => ((nat => bool) => bool list)
                        => (nat => bool) => bool)
               f ((alg_cover::bool list list => (nat => bool) => bool list)
                   l))
             ((algebra_embed::bool list list => (nat => bool) => bool)
               ((filter::(bool list => bool)
                         => bool list list => bool list list)
                 f l)))))"
  by (import prob_indep ALG_COVER_HEAD)

lemma ALG_COVER_TAIL_STEP: "(All::(bool list list => bool) => bool)
 (%l1::bool list list.
     (All::(bool list list => bool) => bool)
      (%l2::bool list list.
          (All::(((nat => bool) => bool) => bool) => bool)
           (%q::(nat => bool) => bool.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((alg_cover_set::bool list list => bool) l1)
                  ((alg_cover_set::bool list list => bool) l2))
                ((op =::((nat => bool) => bool)
                        => ((nat => bool) => bool) => bool)
                  ((op o::((nat => bool) => bool)
                          => ((nat => bool) => nat => bool)
                             => (nat => bool) => bool)
                    q (%x::nat => bool.
                          (SDROP::nat => (nat => bool) => nat => bool)
                           ((size::bool list => nat)
                             ((alg_cover::bool list list
    => (nat => bool) => bool list)
                               ((op @::bool list list
 => bool list list => bool list list)
                                 ((map::(bool list => bool list)
  => bool list list => bool list list)
                                   ((op #::bool => bool list => bool list)
                                     (True::bool))
                                   l1)
                                 ((map::(bool list => bool list)
  => bool list list => bool list list)
                                   ((op #::bool => bool list => bool list)
                                     (False::bool))
                                   l2))
                               x))
                           x))
                  ((pred_set.UNION::((nat => bool) => bool)
                                    => ((nat => bool) => bool)
 => (nat => bool) => bool)
                    ((pred_set.INTER::((nat => bool) => bool)
=> ((nat => bool) => bool) => (nat => bool) => bool)
                      (%x::nat => bool.
                          (op =::bool => bool => bool)
                           ((SHD::(nat => bool) => bool) x) (True::bool))
                      ((op o::((nat => bool) => bool)
                              => ((nat => bool) => nat => bool)
                                 => (nat => bool) => bool)
                        q ((op o::((nat => bool) => nat => bool)
                                  => ((nat => bool) => nat => bool)
                                     => (nat => bool) => nat => bool)
                            (%x::nat => bool.
                                (SDROP::nat => (nat => bool) => nat => bool)
                                 ((size::bool list => nat)
                                   ((alg_cover::bool list list
          => (nat => bool) => bool list)
                                     l1 x))
                                 x)
                            (STL::(nat => bool) => nat => bool))))
                    ((pred_set.INTER::((nat => bool) => bool)
=> ((nat => bool) => bool) => (nat => bool) => bool)
                      (%x::nat => bool.
                          (op =::bool => bool => bool)
                           ((SHD::(nat => bool) => bool) x) (False::bool))
                      ((op o::((nat => bool) => bool)
                              => ((nat => bool) => nat => bool)
                                 => (nat => bool) => bool)
                        q ((op o::((nat => bool) => nat => bool)
                                  => ((nat => bool) => nat => bool)
                                     => (nat => bool) => nat => bool)
                            (%x::nat => bool.
                                (SDROP::nat => (nat => bool) => nat => bool)
                                 ((size::bool list => nat)
                                   ((alg_cover::bool list list
          => (nat => bool) => bool list)
                                     l2 x))
                                 x)
                            (STL::(nat => bool) => nat => bool)))))))))"
  by (import prob_indep ALG_COVER_TAIL_STEP)

lemma ALG_COVER_TAIL_MEASURABLE: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((alg_cover_set::bool list list => bool) l)
      ((All::(((nat => bool) => bool) => bool) => bool)
        (%q::(nat => bool) => bool.
            (op =::bool => bool => bool)
             ((measurable::((nat => bool) => bool) => bool)
               ((op o::((nat => bool) => bool)
                       => ((nat => bool) => nat => bool)
                          => (nat => bool) => bool)
                 q (%x::nat => bool.
                       (SDROP::nat => (nat => bool) => nat => bool)
                        ((size::bool list => nat)
                          ((alg_cover::bool list list
 => (nat => bool) => bool list)
                            l x))
                        x)))
             ((measurable::((nat => bool) => bool) => bool) q))))"
  by (import prob_indep ALG_COVER_TAIL_MEASURABLE)

lemma ALG_COVER_TAIL_PROB: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((alg_cover_set::bool list list => bool) l)
      ((All::(((nat => bool) => bool) => bool) => bool)
        (%q::(nat => bool) => bool.
            (op -->::bool => bool => bool)
             ((measurable::((nat => bool) => bool) => bool) q)
             ((op =::real => real => bool)
               ((prob::((nat => bool) => bool) => real)
                 ((op o::((nat => bool) => bool)
                         => ((nat => bool) => nat => bool)
                            => (nat => bool) => bool)
                   q (%x::nat => bool.
                         (SDROP::nat => (nat => bool) => nat => bool)
                          ((size::bool list => nat)
                            ((alg_cover::bool list list
   => (nat => bool) => bool list)
                              l x))
                          x)))
               ((prob::((nat => bool) => bool) => real) q)))))"
  by (import prob_indep ALG_COVER_TAIL_PROB)

lemma INDEP_INDEP_SET_LEMMA: "(All::(bool list list => bool) => bool)
 (%l::bool list list.
     (op -->::bool => bool => bool)
      ((alg_cover_set::bool list list => bool) l)
      ((All::(((nat => bool) => bool) => bool) => bool)
        (%q::(nat => bool) => bool.
            (op -->::bool => bool => bool)
             ((measurable::((nat => bool) => bool) => bool) q)
             ((All::(bool list => bool) => bool)
               (%x::bool list.
                   (op -->::bool => bool => bool)
                    ((op mem::bool list => bool list list => bool) x l)
                    ((op =::real => real => bool)
                      ((prob::((nat => bool) => bool) => real)
                        ((pred_set.INTER::((nat => bool) => bool)
    => ((nat => bool) => bool) => (nat => bool) => bool)
                          ((alg_embed::bool list => (nat => bool) => bool)
                            x)
                          ((op o::((nat => bool) => bool)
                                  => ((nat => bool) => nat => bool)
                                     => (nat => bool) => bool)
                            q (%x::nat => bool.
                                  (SDROP::nat
    => (nat => bool) => nat => bool)
                                   ((size::bool list => nat)
                                     ((alg_cover::bool list list
            => (nat => bool) => bool list)
 l x))
                                   x))))
                      ((op *::real => real => real)
                        ((op ^::real => nat => real)
                          ((op /::real => real => real) (1::real)
                            ((number_of::bin => real)
                              ((op BIT::bin => bool => bin)
                                ((op BIT::bin => bool => bin) (bin.Pls::bin)
                                  (True::bool))
                                (False::bool))))
                          ((size::bool list => nat) x))
                        ((prob::((nat => bool) => bool) => real) q))))))))"
  by (import prob_indep INDEP_INDEP_SET_LEMMA)

lemma INDEP_SET_LIST: "(All::(((nat => bool) => bool) => bool) => bool)
 (%q::(nat => bool) => bool.
     (All::(bool list list => bool) => bool)
      (%l::bool list list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((alg_sorted::bool list list => bool) l)
             ((op &::bool => bool => bool)
               ((alg_prefixfree::bool list list => bool) l)
               ((op &::bool => bool => bool)
                 ((measurable::((nat => bool) => bool) => bool) q)
                 ((All::(bool list => bool) => bool)
                   (%x::bool list.
                       (op -->::bool => bool => bool)
                        ((op mem::bool list => bool list list => bool) x l)
                        ((indep_set::((nat => bool) => bool)
                                     => ((nat => bool) => bool) => bool)
                          ((alg_embed::bool list => (nat => bool) => bool)
                            x)
                          q))))))
           ((indep_set::((nat => bool) => bool)
                        => ((nat => bool) => bool) => bool)
             ((algebra_embed::bool list list => (nat => bool) => bool) l)
             q)))"
  by (import prob_indep INDEP_SET_LIST)

lemma INDEP_INDEP_SET: "(All::(((nat => bool) => 'a * (nat => bool)) => bool) => bool)
 (%f::(nat => bool) => 'a * (nat => bool).
     (All::(('a => bool) => bool) => bool)
      (%p::'a => bool.
          (All::(((nat => bool) => bool) => bool) => bool)
           (%q::(nat => bool) => bool.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((indep::((nat => bool) => 'a * (nat => bool)) => bool) f)
                  ((measurable::((nat => bool) => bool) => bool) q))
                ((indep_set::((nat => bool) => bool)
                             => ((nat => bool) => bool) => bool)
                  ((op o::('a => bool)
                          => ((nat => bool) => 'a) => (nat => bool) => bool)
                    p ((op o::('a * (nat => bool) => 'a)
                              => ((nat => bool) => 'a * (nat => bool))
                                 => (nat => bool) => 'a)
                        (fst::'a * (nat => bool) => 'a) f))
                  ((op o::((nat => bool) => bool)
                          => ((nat => bool) => nat => bool)
                             => (nat => bool) => bool)
                    q ((op o::('a * (nat => bool) => nat => bool)
                              => ((nat => bool) => 'a * (nat => bool))
                                 => (nat => bool) => nat => bool)
                        (snd::'a * (nat => bool) => nat => bool) f))))))"
  by (import prob_indep INDEP_INDEP_SET)

lemma INDEP_UNIT: "ALL x. indep (UNIT x)"
  by (import prob_indep INDEP_UNIT)

lemma INDEP_SDEST: "indep SDEST"
  by (import prob_indep INDEP_SDEST)

lemma BIND_STEP: "ALL f. BIND SDEST (%k. f o SCONS k) = f"
  by (import prob_indep BIND_STEP)

lemma INDEP_BIND_SDEST: "(All::((bool => (nat => bool) => 'a * (nat => bool)) => bool) => bool)
 (%f::bool => (nat => bool) => 'a * (nat => bool).
     (op -->::bool => bool => bool)
      ((All::(bool => bool) => bool)
        (%x::bool.
            (indep::((nat => bool) => 'a * (nat => bool)) => bool) (f x)))
      ((indep::((nat => bool) => 'a * (nat => bool)) => bool)
        ((BIND::((nat => bool) => bool * (nat => bool))
                => (bool => (nat => bool) => 'a * (nat => bool))
                   => (nat => bool) => 'a * (nat => bool))
          (SDEST::(nat => bool) => bool * (nat => bool)) f)))"
  by (import prob_indep INDEP_BIND_SDEST)

lemma INDEP_BIND: "(All::(((nat => bool) => 'a * (nat => bool)) => bool) => bool)
 (%f::(nat => bool) => 'a * (nat => bool).
     (All::(('a => (nat => bool) => 'b * (nat => bool)) => bool) => bool)
      (%g::'a => (nat => bool) => 'b * (nat => bool).
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((indep::((nat => bool) => 'a * (nat => bool)) => bool) f)
             ((All::('a => bool) => bool)
               (%x::'a.
                   (indep::((nat => bool) => 'b * (nat => bool)) => bool)
                    (g x))))
           ((indep::((nat => bool) => 'b * (nat => bool)) => bool)
             ((BIND::((nat => bool) => 'a * (nat => bool))
                     => ('a => (nat => bool) => 'b * (nat => bool))
                        => (nat => bool) => 'b * (nat => bool))
               f g))))"
  by (import prob_indep INDEP_BIND)

lemma INDEP_PROB: "(All::(((nat => bool) => 'a * (nat => bool)) => bool) => bool)
 (%f::(nat => bool) => 'a * (nat => bool).
     (All::(('a => bool) => bool) => bool)
      (%p::'a => bool.
          (All::(((nat => bool) => bool) => bool) => bool)
           (%q::(nat => bool) => bool.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((indep::((nat => bool) => 'a * (nat => bool)) => bool) f)
                  ((measurable::((nat => bool) => bool) => bool) q))
                ((op =::real => real => bool)
                  ((prob::((nat => bool) => bool) => real)
                    ((pred_set.INTER::((nat => bool) => bool)
=> ((nat => bool) => bool) => (nat => bool) => bool)
                      ((op o::('a => bool)
                              => ((nat => bool) => 'a)
                                 => (nat => bool) => bool)
                        p ((op o::('a * (nat => bool) => 'a)
                                  => ((nat => bool) => 'a * (nat => bool))
                                     => (nat => bool) => 'a)
                            (fst::'a * (nat => bool) => 'a) f))
                      ((op o::((nat => bool) => bool)
                              => ((nat => bool) => nat => bool)
                                 => (nat => bool) => bool)
                        q ((op o::('a * (nat => bool) => nat => bool)
                                  => ((nat => bool) => 'a * (nat => bool))
                                     => (nat => bool) => nat => bool)
                            (snd::'a * (nat => bool) => nat => bool) f))))
                  ((op *::real => real => real)
                    ((prob::((nat => bool) => bool) => real)
                      ((op o::('a => bool)
                              => ((nat => bool) => 'a)
                                 => (nat => bool) => bool)
                        p ((op o::('a * (nat => bool) => 'a)
                                  => ((nat => bool) => 'a * (nat => bool))
                                     => (nat => bool) => 'a)
                            (fst::'a * (nat => bool) => 'a) f)))
                    ((prob::((nat => bool) => bool) => real) q))))))"
  by (import prob_indep INDEP_PROB)

lemma INDEP_MEASURABLE1: "(All::(((nat => bool) => 'a * (nat => bool)) => bool) => bool)
 (%f::(nat => bool) => 'a * (nat => bool).
     (All::(('a => bool) => bool) => bool)
      (%p::'a => bool.
          (op -->::bool => bool => bool)
           ((indep::((nat => bool) => 'a * (nat => bool)) => bool) f)
           ((measurable::((nat => bool) => bool) => bool)
             ((op o::('a => bool)
                     => ((nat => bool) => 'a) => (nat => bool) => bool)
               p ((op o::('a * (nat => bool) => 'a)
                         => ((nat => bool) => 'a * (nat => bool))
                            => (nat => bool) => 'a)
                   (fst::'a * (nat => bool) => 'a) f)))))"
  by (import prob_indep INDEP_MEASURABLE1)

lemma INDEP_MEASURABLE2: "(All::(((nat => bool) => 'a * (nat => bool)) => bool) => bool)
 (%f::(nat => bool) => 'a * (nat => bool).
     (All::(((nat => bool) => bool) => bool) => bool)
      (%q::(nat => bool) => bool.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((indep::((nat => bool) => 'a * (nat => bool)) => bool) f)
             ((measurable::((nat => bool) => bool) => bool) q))
           ((measurable::((nat => bool) => bool) => bool)
             ((op o::((nat => bool) => bool)
                     => ((nat => bool) => nat => bool)
                        => (nat => bool) => bool)
               q ((op o::('a * (nat => bool) => nat => bool)
                         => ((nat => bool) => 'a * (nat => bool))
                            => (nat => bool) => nat => bool)
                   (snd::'a * (nat => bool) => nat => bool) f)))))"
  by (import prob_indep INDEP_MEASURABLE2)

lemma PROB_INDEP_BOUND: "(All::(((nat => bool) => nat * (nat => bool)) => bool) => bool)
 (%f::(nat => bool) => nat * (nat => bool).
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool)
           ((indep::((nat => bool) => nat * (nat => bool)) => bool) f)
           ((op =::real => real => bool)
             ((prob::((nat => bool) => bool) => real)
               (%s::nat => bool.
                   (op <::nat => nat => bool)
                    ((fst::nat * (nat => bool) => nat) (f s))
                    ((Suc::nat => nat) n)))
             ((op +::real => real => real)
               ((prob::((nat => bool) => bool) => real)
                 (%s::nat => bool.
                     (op <::nat => nat => bool)
                      ((fst::nat * (nat => bool) => nat) (f s)) n))
               ((prob::((nat => bool) => bool) => real)
                 (%s::nat => bool.
                     (op =::nat => nat => bool)
                      ((fst::nat * (nat => bool) => nat) (f s)) n))))))"
  by (import prob_indep PROB_INDEP_BOUND)

;end_setup

;setup_theory prob_uniform

consts
  unif_bound :: "nat => nat" 

defs
  unif_bound_primdef: "unif_bound ==
WFREC (SOME R. WF R & (ALL v. R (Suc v div 2) (Suc v)))
 (%unif_bound. nat_case 0 (%v1. Suc (unif_bound (Suc v1 div 2))))"

lemma unif_bound_primitive_def: "unif_bound =
WFREC (SOME R. WF R & (ALL v. R (Suc v div 2) (Suc v)))
 (%unif_bound. nat_case 0 (%v1. Suc (unif_bound (Suc v1 div 2))))"
  by (import prob_uniform unif_bound_primitive_def)

lemma unif_bound_def: "unif_bound 0 = 0 & unif_bound (Suc v) = Suc (unif_bound (Suc v div 2))"
  by (import prob_uniform unif_bound_def)

lemma unif_bound_ind: "(All::((nat => bool) => bool) => bool)
 (%P::nat => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) (P (0::nat))
        ((All::(nat => bool) => bool)
          (%v::nat.
              (op -->::bool => bool => bool)
               (P ((op div::nat => nat => nat) ((Suc::nat => nat) v)
                    ((number_of::bin => nat)
                      ((op BIT::bin => bool => bin)
                        ((op BIT::bin => bool => bin) (bin.Pls::bin)
                          (True::bool))
                        (False::bool)))))
               (P ((Suc::nat => nat) v)))))
      ((All::(nat => bool) => bool) P))"
  by (import prob_uniform unif_bound_ind)

constdefs
  unif_tupled :: "nat * (nat => bool) => nat * (nat => bool)" 
  "unif_tupled ==
WFREC (SOME R. WF R & (ALL s v2. R (Suc v2 div 2, s) (Suc v2, s)))
 (%unif_tupled (v, v1).
     case v of 0 => (0, v1)
     | Suc v3 =>
         let (m, s') = unif_tupled (Suc v3 div 2, v1)
         in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))"

lemma unif_tupled_primitive_def: "unif_tupled =
WFREC (SOME R. WF R & (ALL s v2. R (Suc v2 div 2, s) (Suc v2, s)))
 (%unif_tupled (v, v1).
     case v of 0 => (0, v1)
     | Suc v3 =>
         let (m, s') = unif_tupled (Suc v3 div 2, v1)
         in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))"
  by (import prob_uniform unif_tupled_primitive_def)

consts
  unif :: "nat => (nat => bool) => nat * (nat => bool)" 

defs
  unif_primdef: "unif == %x x1. unif_tupled (x, x1)"

lemma unif_curried_def: "ALL x x1. unif x x1 = unif_tupled (x, x1)"
  by (import prob_uniform unif_curried_def)

lemma unif_def: "unif 0 s = (0, s) &
unif (Suc v2) s =
(let (m, s') = unif (Suc v2 div 2) s
 in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))"
  by (import prob_uniform unif_def)

lemma unif_ind: "(All::((nat => (nat => bool) => bool) => bool) => bool)
 (%P::nat => (nat => bool) => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((All::((nat => bool) => bool) => bool) (P (0::nat)))
        ((All::(nat => bool) => bool)
          (%v2::nat.
              (All::((nat => bool) => bool) => bool)
               (%s::nat => bool.
                   (op -->::bool => bool => bool)
                    (P ((op div::nat => nat => nat) ((Suc::nat => nat) v2)
                         ((number_of::bin => nat)
                           ((op BIT::bin => bool => bin)
                             ((op BIT::bin => bool => bin) (bin.Pls::bin)
                               (True::bool))
                             (False::bool))))
                      s)
                    (P ((Suc::nat => nat) v2) s)))))
      ((All::(nat => bool) => bool)
        (%v::nat. (All::((nat => bool) => bool) => bool) (P v))))"
  by (import prob_uniform unif_ind)

constdefs
  uniform_tupled :: "nat * nat * (nat => bool) => nat * (nat => bool)" 
  "(op ==::(nat * nat * (nat => bool) => nat * (nat => bool))
        => (nat * nat * (nat => bool) => nat * (nat => bool)) => prop)
 (uniform_tupled::nat * nat * (nat => bool) => nat * (nat => bool))
 ((WFREC::(nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool)
          => ((nat * nat * (nat => bool) => nat * (nat => bool))
              => nat * nat * (nat => bool) => nat * (nat => bool))
             => nat * nat * (nat => bool) => nat * (nat => bool))
   ((Eps::((nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool)
           => bool)
          => nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool)
     (%R::nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool.
         (op &::bool => bool => bool)
          ((WF::(nat * nat * (nat => bool)
                 => nat * nat * (nat => bool) => bool)
                => bool)
            R)
          ((All::(nat => bool) => bool)
            (%t::nat.
                (All::((nat => bool) => bool) => bool)
                 (%s::nat => bool.
                     (All::(nat => bool) => bool)
                      (%n::nat.
                          (All::(nat => bool) => bool)
                           (%res::nat.
                               (All::((nat => bool) => bool) => bool)
                                (%s'::nat => bool.
                                    (op -->::bool => bool => bool)
                                     ((op &::bool => bool => bool)
 ((op =::nat * (nat => bool) => nat * (nat => bool) => bool)
   ((Pair::nat => (nat => bool) => nat * (nat => bool)) res s')
   ((unif::nat => (nat => bool) => nat * (nat => bool)) n s))
 ((Not::bool => bool)
   ((op <::nat => nat => bool) res ((Suc::nat => nat) n))))
                                     (R
 ((Pair::nat => nat * (nat => bool) => nat * nat * (nat => bool)) t
   ((Pair::nat => (nat => bool) => nat * (nat => bool))
     ((Suc::nat => nat) n) s'))
 ((Pair::nat => nat * (nat => bool) => nat * nat * (nat => bool))
   ((Suc::nat => nat) t)
   ((Pair::nat => (nat => bool) => nat * (nat => bool))
     ((Suc::nat => nat) n) s)))))))))))
   (%uniform_tupled::nat * nat * (nat => bool) => nat * (nat => bool).
       (split::(nat => nat * (nat => bool) => nat * (nat => bool))
               => nat * nat * (nat => bool) => nat * (nat => bool))
        (%(v::nat) v1::nat * (nat => bool).
            (nat_case::nat * (nat => bool)
                       => (nat => nat * (nat => bool))
                          => nat => nat * (nat => bool))
             ((split::(nat => (nat => bool) => nat * (nat => bool))
                      => nat * (nat => bool) => nat * (nat => bool))
               (%(v3::nat) v4::nat => bool.
                   (nat_case::nat * (nat => bool)
                              => (nat => nat * (nat => bool))
                                 => nat => nat * (nat => bool))
                    (ARB::nat * (nat => bool))
                    (%v5::nat.
                        (Pair::nat => (nat => bool) => nat * (nat => bool))
                         (0::nat) v4)
                    v3)
               v1)
             (%v2::nat.
                 (split::(nat => (nat => bool) => nat * (nat => bool))
                         => nat * (nat => bool) => nat * (nat => bool))
                  (%(v7::nat) v8::nat => bool.
                      (nat_case::nat * (nat => bool)
                                 => (nat => nat * (nat => bool))
                                    => nat => nat * (nat => bool))
                       (ARB::nat * (nat => bool))
                       (%v9::nat.
                           (Let::nat * (nat => bool)
                                 => (nat * (nat => bool)
                                     => nat * (nat => bool))
                                    => nat * (nat => bool))
                            ((unif::nat
                                    => (nat => bool) => nat * (nat => bool))
                              v9 v8)
                            ((split::(nat
=> (nat => bool) => nat * (nat => bool))
                                     => nat * (nat => bool)
  => nat * (nat => bool))
                              (%(res::nat) s'::nat => bool.
                                  (If::bool
 => nat * (nat => bool) => nat * (nat => bool) => nat * (nat => bool))
                                   ((op <::nat => nat => bool) res
                                     ((Suc::nat => nat) v9))
                                   ((Pair::nat
     => (nat => bool) => nat * (nat => bool))
                                     res s')
                                   (uniform_tupled
                                     ((Pair::nat
       => nat * (nat => bool) => nat * nat * (nat => bool))
 v2 ((Pair::nat => (nat => bool) => nat * (nat => bool))
      ((Suc::nat => nat) v9) s'))))))
                       v7)
                  v1)
             v)))"

lemma uniform_tupled_primitive_def: "(op =::(nat * nat * (nat => bool) => nat * (nat => bool))
       => (nat * nat * (nat => bool) => nat * (nat => bool)) => bool)
 (uniform_tupled::nat * nat * (nat => bool) => nat * (nat => bool))
 ((WFREC::(nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool)
          => ((nat * nat * (nat => bool) => nat * (nat => bool))
              => nat * nat * (nat => bool) => nat * (nat => bool))
             => nat * nat * (nat => bool) => nat * (nat => bool))
   ((Eps::((nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool)
           => bool)
          => nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool)
     (%R::nat * nat * (nat => bool) => nat * nat * (nat => bool) => bool.
         (op &::bool => bool => bool)
          ((WF::(nat * nat * (nat => bool)
                 => nat * nat * (nat => bool) => bool)
                => bool)
            R)
          ((All::(nat => bool) => bool)
            (%t::nat.
                (All::((nat => bool) => bool) => bool)
                 (%s::nat => bool.
                     (All::(nat => bool) => bool)
                      (%n::nat.
                          (All::(nat => bool) => bool)
                           (%res::nat.
                               (All::((nat => bool) => bool) => bool)
                                (%s'::nat => bool.
                                    (op -->::bool => bool => bool)
                                     ((op &::bool => bool => bool)
 ((op =::nat * (nat => bool) => nat * (nat => bool) => bool)
   ((Pair::nat => (nat => bool) => nat * (nat => bool)) res s')
   ((unif::nat => (nat => bool) => nat * (nat => bool)) n s))
 ((Not::bool => bool)
   ((op <::nat => nat => bool) res ((Suc::nat => nat) n))))
                                     (R
 ((Pair::nat => nat * (nat => bool) => nat * nat * (nat => bool)) t
   ((Pair::nat => (nat => bool) => nat * (nat => bool))
     ((Suc::nat => nat) n) s'))
 ((Pair::nat => nat * (nat => bool) => nat * nat * (nat => bool))
   ((Suc::nat => nat) t)
   ((Pair::nat => (nat => bool) => nat * (nat => bool))
     ((Suc::nat => nat) n) s)))))))))))
   (%uniform_tupled::nat * nat * (nat => bool) => nat * (nat => bool).
       (split::(nat => nat * (nat => bool) => nat * (nat => bool))
               => nat * nat * (nat => bool) => nat * (nat => bool))
        (%(v::nat) v1::nat * (nat => bool).
            (nat_case::nat * (nat => bool)
                       => (nat => nat * (nat => bool))
                          => nat => nat * (nat => bool))
             ((split::(nat => (nat => bool) => nat * (nat => bool))
                      => nat * (nat => bool) => nat * (nat => bool))
               (%(v3::nat) v4::nat => bool.
                   (nat_case::nat * (nat => bool)
                              => (nat => nat * (nat => bool))
                                 => nat => nat * (nat => bool))
                    (ARB::nat * (nat => bool))
                    (%v5::nat.
                        (Pair::nat => (nat => bool) => nat * (nat => bool))
                         (0::nat) v4)
                    v3)
               v1)
             (%v2::nat.
                 (split::(nat => (nat => bool) => nat * (nat => bool))
                         => nat * (nat => bool) => nat * (nat => bool))
                  (%(v7::nat) v8::nat => bool.
                      (nat_case::nat * (nat => bool)
                                 => (nat => nat * (nat => bool))
                                    => nat => nat * (nat => bool))
                       (ARB::nat * (nat => bool))
                       (%v9::nat.
                           (Let::nat * (nat => bool)
                                 => (nat * (nat => bool)
                                     => nat * (nat => bool))
                                    => nat * (nat => bool))
                            ((unif::nat
                                    => (nat => bool) => nat * (nat => bool))
                              v9 v8)
                            ((split::(nat
=> (nat => bool) => nat * (nat => bool))
                                     => nat * (nat => bool)
  => nat * (nat => bool))
                              (%(res::nat) s'::nat => bool.
                                  (If::bool
 => nat * (nat => bool) => nat * (nat => bool) => nat * (nat => bool))
                                   ((op <::nat => nat => bool) res
                                     ((Suc::nat => nat) v9))
                                   ((Pair::nat
     => (nat => bool) => nat * (nat => bool))
                                     res s')
                                   (uniform_tupled
                                     ((Pair::nat
       => nat * (nat => bool) => nat * nat * (nat => bool))
 v2 ((Pair::nat => (nat => bool) => nat * (nat => bool))
      ((Suc::nat => nat) v9) s'))))))
                       v7)
                  v1)
             v)))"
  by (import prob_uniform uniform_tupled_primitive_def)

consts
  uniform :: "nat => nat => (nat => bool) => nat * (nat => bool)" 

defs
  uniform_primdef: "uniform == %x x1 x2. uniform_tupled (x, x1, x2)"

lemma uniform_curried_def: "ALL x x1 x2. uniform x x1 x2 = uniform_tupled (x, x1, x2)"
  by (import prob_uniform uniform_curried_def)

lemma uniform_ind: "(All::((nat => nat => (nat => bool) => bool) => bool) => bool)
 (%P::nat => nat => (nat => bool) => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((All::(nat => bool) => bool)
          (%x::nat.
              (All::((nat => bool) => bool) => bool)
               (P ((Suc::nat => nat) x) (0::nat))))
        ((op &::bool => bool => bool)
          ((All::((nat => bool) => bool) => bool) (P (0::nat) (0::nat)))
          ((op &::bool => bool => bool)
            ((All::(nat => bool) => bool)
              (%x::nat.
                  (All::((nat => bool) => bool) => bool)
                   (P (0::nat) ((Suc::nat => nat) x))))
            ((All::(nat => bool) => bool)
              (%x::nat.
                  (All::(nat => bool) => bool)
                   (%xa::nat.
                       (All::((nat => bool) => bool) => bool)
                        (%xb::nat => bool.
                            (op -->::bool => bool => bool)
                             ((All::(nat => bool) => bool)
                               (%xc::nat.
                                   (All::((nat => bool) => bool) => bool)
                                    (%xd::nat => bool.
  (op -->::bool => bool => bool)
   ((op &::bool => bool => bool)
     ((op =::nat * (nat => bool) => nat * (nat => bool) => bool)
       ((Pair::nat => (nat => bool) => nat * (nat => bool)) xc xd)
       ((unif::nat => (nat => bool) => nat * (nat => bool)) xa xb))
     ((Not::bool => bool)
       ((op <::nat => nat => bool) xc ((Suc::nat => nat) xa))))
   (P x ((Suc::nat => nat) xa) xd))))
                             (P ((Suc::nat => nat) x) ((Suc::nat => nat) xa)
                               xb))))))))
      ((All::(nat => bool) => bool)
        (%x::nat.
            (All::(nat => bool) => bool)
             (%xa::nat. (All::((nat => bool) => bool) => bool) (P x xa)))))"
  by (import prob_uniform uniform_ind)

lemma uniform_def: "uniform 0 (Suc n) s = (0, s) &
uniform (Suc t) (Suc n) s =
(let (xa, x) = unif n s
 in if xa < Suc n then (xa, x) else uniform t (Suc n) x)"
  by (import prob_uniform uniform_def)

lemma SUC_DIV_TWO_ZERO: "ALL n. (Suc n div 2 = 0) = (n = 0)"
  by (import prob_uniform SUC_DIV_TWO_ZERO)

lemma UNIF_BOUND_LOWER: "ALL n. n < 2 ^ unif_bound n"
  by (import prob_uniform UNIF_BOUND_LOWER)

lemma UNIF_BOUND_LOWER_SUC: "ALL n. Suc n <= 2 ^ unif_bound n"
  by (import prob_uniform UNIF_BOUND_LOWER_SUC)

lemma UNIF_BOUND_UPPER: "(All::(nat => bool) => bool)
 (%n::nat.
     (op -->::bool => bool => bool)
      ((Not::bool => bool) ((op =::nat => nat => bool) n (0::nat)))
      ((op <=::nat => nat => bool)
        ((op ^::nat => nat => nat)
          ((number_of::bin => nat)
            ((op BIT::bin => bool => bin)
              ((op BIT::bin => bool => bin) (bin.Pls::bin) (True::bool))
              (False::bool)))
          ((unif_bound::nat => nat) n))
        ((op *::nat => nat => nat)
          ((number_of::bin => nat)
            ((op BIT::bin => bool => bin)
              ((op BIT::bin => bool => bin) (bin.Pls::bin) (True::bool))
              (False::bool)))
          n)))"
  by (import prob_uniform UNIF_BOUND_UPPER)

lemma UNIF_BOUND_UPPER_SUC: "ALL n. 2 ^ unif_bound n <= Suc (2 * n)"
  by (import prob_uniform UNIF_BOUND_UPPER_SUC)

lemma UNIF_DEF_MONAD: "unif 0 = UNIT 0 &
(ALL n.
    unif (Suc n) =
    BIND (unif (Suc n div 2))
     (%m. BIND SDEST (%b. UNIT (if b then 2 * m + 1 else 2 * m))))"
  by (import prob_uniform UNIF_DEF_MONAD)

lemma UNIFORM_DEF_MONAD: "(ALL x. uniform 0 (Suc x) = UNIT 0) &
(ALL x xa.
    uniform (Suc x) (Suc xa) =
    BIND (unif xa) (%m. if m < Suc xa then UNIT m else uniform x (Suc xa)))"
  by (import prob_uniform UNIFORM_DEF_MONAD)

lemma INDEP_UNIF: "ALL n. indep (unif n)"
  by (import prob_uniform INDEP_UNIF)

lemma INDEP_UNIFORM: "ALL t n. indep (uniform t (Suc n))"
  by (import prob_uniform INDEP_UNIFORM)

lemma PROB_UNIF: "ALL n k.
   prob (%s. fst (unif n s) = k) =
   (if k < 2 ^ unif_bound n then (1 / 2) ^ unif_bound n else 0)"
  by (import prob_uniform PROB_UNIF)

lemma UNIF_RANGE: "ALL n s. fst (unif n s) < 2 ^ unif_bound n"
  by (import prob_uniform UNIF_RANGE)

lemma PROB_UNIF_PAIR: "ALL n k k'.
   (prob (%s. fst (unif n s) = k) = prob (%s. fst (unif n s) = k')) =
   ((k < 2 ^ unif_bound n) = (k' < 2 ^ unif_bound n))"
  by (import prob_uniform PROB_UNIF_PAIR)

lemma PROB_UNIF_BOUND: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(nat => bool) => bool)
      (%k::nat.
          (op -->::bool => bool => bool)
           ((op <=::nat => nat => bool) k
             ((op ^::nat => nat => nat)
               ((number_of::bin => nat)
                 ((op BIT::bin => bool => bin)
                   ((op BIT::bin => bool => bin) (bin.Pls::bin)
                     (True::bool))
                   (False::bool)))
               ((unif_bound::nat => nat) n)))
           ((op =::real => real => bool)
             ((prob::((nat => bool) => bool) => real)
               (%s::nat => bool.
                   (op <::nat => nat => bool)
                    ((fst::nat * (nat => bool) => nat)
                      ((unif::nat => (nat => bool) => nat * (nat => bool)) n
                        s))
                    k))
             ((op *::real => real => real) ((real::nat => real) k)
               ((op ^::real => nat => real)
                 ((op /::real => real => real) (1::real)
                   ((number_of::bin => real)
                     ((op BIT::bin => bool => bin)
                       ((op BIT::bin => bool => bin) (bin.Pls::bin)
                         (True::bool))
                       (False::bool))))
                 ((unif_bound::nat => nat) n))))))"
  by (import prob_uniform PROB_UNIF_BOUND)

lemma PROB_UNIF_GOOD: "ALL n. 1 / 2 <= prob (%s. fst (unif n s) < Suc n)"
  by (import prob_uniform PROB_UNIF_GOOD)

lemma UNIFORM_RANGE: "ALL t n s. fst (uniform t (Suc n) s) < Suc n"
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

lemma PROB_UNIFORM_PAIR_SUC: "(All::(nat => bool) => bool)
 (%t::nat.
     (All::(nat => bool) => bool)
      (%n::nat.
          (All::(nat => bool) => bool)
           (%k::nat.
               (All::(nat => bool) => bool)
                (%k'::nat.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <::nat => nat => bool) k ((Suc::nat => nat) n))
                       ((op <::nat => nat => bool) k'
                         ((Suc::nat => nat) n)))
                     ((op <=::real => real => bool)
                       ((abs::real => real)
                         ((op -::real => real => real)
                           ((prob::((nat => bool) => bool) => real)
                             (%s::nat => bool.
                                 (op =::nat => nat => bool)
                                  ((fst::nat * (nat => bool) => nat)
                                    ((uniform::nat
         => nat => (nat => bool) => nat * (nat => bool))
t ((Suc::nat => nat) n) s))
                                  k))
                           ((prob::((nat => bool) => bool) => real)
                             (%s::nat => bool.
                                 (op =::nat => nat => bool)
                                  ((fst::nat * (nat => bool) => nat)
                                    ((uniform::nat
         => nat => (nat => bool) => nat * (nat => bool))
t ((Suc::nat => nat) n) s))
                                  k'))))
                       ((op ^::real => nat => real)
                         ((op /::real => real => real) (1::real)
                           ((number_of::bin => real)
                             ((op BIT::bin => bool => bin)
                               ((op BIT::bin => bool => bin) (bin.Pls::bin)
                                 (True::bool))
                               (False::bool))))
                         t))))))"
  by (import prob_uniform PROB_UNIFORM_PAIR_SUC)

lemma PROB_UNIFORM_SUC: "(All::(nat => bool) => bool)
 (%t::nat.
     (All::(nat => bool) => bool)
      (%n::nat.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) k ((Suc::nat => nat) n))
                ((op <=::real => real => bool)
                  ((abs::real => real)
                    ((op -::real => real => real)
                      ((prob::((nat => bool) => bool) => real)
                        (%s::nat => bool.
                            (op =::nat => nat => bool)
                             ((fst::nat * (nat => bool) => nat)
                               ((uniform::nat
    => nat => (nat => bool) => nat * (nat => bool))
                                 t ((Suc::nat => nat) n) s))
                             k))
                      ((op /::real => real => real) (1::real)
                        ((real::nat => real) ((Suc::nat => nat) n)))))
                  ((op ^::real => nat => real)
                    ((op /::real => real => real) (1::real)
                      ((number_of::bin => real)
                        ((op BIT::bin => bool => bin)
                          ((op BIT::bin => bool => bin) (bin.Pls::bin)
                            (True::bool))
                          (False::bool))))
                    t)))))"
  by (import prob_uniform PROB_UNIFORM_SUC)

lemma PROB_UNIFORM: "(All::(nat => bool) => bool)
 (%t::nat.
     (All::(nat => bool) => bool)
      (%n::nat.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) k n)
                ((op <=::real => real => bool)
                  ((abs::real => real)
                    ((op -::real => real => real)
                      ((prob::((nat => bool) => bool) => real)
                        (%s::nat => bool.
                            (op =::nat => nat => bool)
                             ((fst::nat * (nat => bool) => nat)
                               ((uniform::nat
    => nat => (nat => bool) => nat * (nat => bool))
                                 t n s))
                             k))
                      ((op /::real => real => real) (1::real)
                        ((real::nat => real) n))))
                  ((op ^::real => nat => real)
                    ((op /::real => real => real) (1::real)
                      ((number_of::bin => real)
                        ((op BIT::bin => bool => bin)
                          ((op BIT::bin => bool => bin) (bin.Pls::bin)
                            (True::bool))
                          (False::bool))))
                    t)))))"
  by (import prob_uniform PROB_UNIFORM)

;end_setup

end

