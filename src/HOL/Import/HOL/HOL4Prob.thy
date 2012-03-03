(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Prob imports HOL4Real begin

setup_theory "~~/src/HOL/Import/HOL" prob_extra

lemma BOOL_BOOL_CASES_THM: "f = (%b. False) | f = (%b. True) | f = (%b. b) | f = Not"
  by (import prob_extra BOOL_BOOL_CASES_THM)

lemma EVEN_ODD_BASIC: "EVEN 0 & ~ EVEN 1 & EVEN 2 & ~ ODD 0 & ODD 1 & ~ ODD 2"
  by (import prob_extra EVEN_ODD_BASIC)

lemma EVEN_ODD_EXISTS_EQ: "EVEN n = (EX m. n = 2 * m) & ODD n = (EX m. n = Suc (2 * m))"
  by (import prob_extra EVEN_ODD_EXISTS_EQ)

lemma DIV_THEN_MULT: "Suc q * (p div Suc q) <= p"
  by (import prob_extra DIV_THEN_MULT)

lemma DIV_TWO_UNIQUE: "(n::nat) = (2::nat) * (q::nat) + (r::nat) & (r = (0::nat) | r = (1::nat))
==> q = n div (2::nat) & r = n mod (2::nat)"
  by (import prob_extra DIV_TWO_UNIQUE)

lemma DIVISION_TWO: "(n::nat) = (2::nat) * (n div (2::nat)) + n mod (2::nat) &
(n mod (2::nat) = (0::nat) | n mod (2::nat) = (1::nat))"
  by (import prob_extra DIVISION_TWO)

lemma DIV_TWO: "(n::nat) = (2::nat) * (n div (2::nat)) + n mod (2::nat)"
  by (import prob_extra DIV_TWO)

lemma MOD_TWO: "n mod 2 = (if EVEN n then 0 else 1)"
  by (import prob_extra MOD_TWO)

lemma DIV_TWO_BASIC: "(0::nat) div (2::nat) = (0::nat) &
(1::nat) div (2::nat) = (0::nat) & (2::nat) div (2::nat) = (1::nat)"
  by (import prob_extra DIV_TWO_BASIC)

lemma DIV_TWO_MONO: "(m::nat) div (2::nat) < (n::nat) div (2::nat) ==> m < n"
  by (import prob_extra DIV_TWO_MONO)

lemma DIV_TWO_MONO_EVEN: "EVEN n ==> (m div 2 < n div 2) = (m < n)"
  by (import prob_extra DIV_TWO_MONO_EVEN)

lemma DIV_TWO_CANCEL: "2 * n div 2 = n & Suc (2 * n) div 2 = n"
  by (import prob_extra DIV_TWO_CANCEL)

lemma EXP_DIV_TWO: "(2::nat) ^ Suc (n::nat) div (2::nat) = (2::nat) ^ n"
  by (import prob_extra EXP_DIV_TWO)

lemma EVEN_EXP_TWO: "EVEN (2 ^ n) = (n ~= 0)"
  by (import prob_extra EVEN_EXP_TWO)

lemma DIV_TWO_EXP: "((k::nat) div (2::nat) < (2::nat) ^ (n::nat)) = (k < (2::nat) ^ Suc n)"
  by (import prob_extra DIV_TWO_EXP)

consts
  inf :: "(real => bool) => real" 

defs
  inf_primdef: "prob_extra.inf == %P. - real.sup (IMAGE uminus P)"

lemma inf_def: "prob_extra.inf P = - real.sup (IMAGE uminus P)"
  by (import prob_extra inf_def)

lemma INF_DEF_ALT: "prob_extra.inf P = - real.sup (%r. P (- r))"
  by (import prob_extra INF_DEF_ALT)

lemma REAL_SUP_EXISTS_UNIQUE: "Ex (P::real => bool) & (EX z::real. ALL x::real. P x --> x <= z)
==> EX! s::real. ALL y::real. (EX x::real. P x & y < x) = (y < s)"
  by (import prob_extra REAL_SUP_EXISTS_UNIQUE)

lemma REAL_SUP_MAX: "P z & (ALL x. P x --> x <= z) ==> real.sup P = z"
  by (import prob_extra REAL_SUP_MAX)

lemma REAL_INF_MIN: "P z & (ALL x. P x --> z <= x) ==> prob_extra.inf P = z"
  by (import prob_extra REAL_INF_MIN)

lemma HALF_CANCEL: "(2::real) * ((1::real) / (2::real)) = (1::real)"
  by (import prob_extra HALF_CANCEL)

lemma POW_HALF_POS: "(0::real) < ((1::real) / (2::real)) ^ (n::nat)"
  by (import prob_extra POW_HALF_POS)

lemma POW_HALF_MONO: "(m::nat) <= (n::nat)
==> ((1::real) / (2::real)) ^ n <= ((1::real) / (2::real)) ^ m"
  by (import prob_extra POW_HALF_MONO)

lemma POW_HALF_TWICE: "((1::real) / (2::real)) ^ (n::nat) =
(2::real) * ((1::real) / (2::real)) ^ Suc n"
  by (import prob_extra POW_HALF_TWICE)

lemma X_HALF_HALF: "(1::real) / (2::real) * (x::real) + (1::real) / (2::real) * x = x"
  by (import prob_extra X_HALF_HALF)

lemma REAL_SUP_LE_X: "Ex P & (ALL r. P r --> r <= x) ==> real.sup P <= x"
  by (import prob_extra REAL_SUP_LE_X)

lemma REAL_X_LE_SUP: "Ex P & (EX z. ALL r. P r --> r <= z) & (EX r. P r & x <= r)
==> x <= real.sup P"
  by (import prob_extra REAL_X_LE_SUP)

lemma ABS_BETWEEN_LE: "((0::real) <= (d::real) & (x::real) - d <= (y::real) & y <= x + d) =
(abs (y - x) <= d)"
  by (import prob_extra ABS_BETWEEN_LE)

lemma ONE_MINUS_HALF: "(1::real) - (1::real) / (2::real) = (1::real) / (2::real)"
  by (import prob_extra ONE_MINUS_HALF)

lemma HALF_LT_1: "(1::real) / (2::real) < (1::real)"
  by (import prob_extra HALF_LT_1)

lemma POW_HALF_EXP: "((1::real) / (2::real)) ^ (n::nat) = inverse (real ((2::nat) ^ n))"
  by (import prob_extra POW_HALF_EXP)

lemma INV_SUC_POS: "0 < 1 / real (Suc n)"
  by (import prob_extra INV_SUC_POS)

lemma INV_SUC_MAX: "1 / real (Suc x) <= 1"
  by (import prob_extra INV_SUC_MAX)

lemma INV_SUC: "0 < 1 / real (Suc n) & 1 / real (Suc n) <= 1"
  by (import prob_extra INV_SUC)

lemma ABS_UNIT_INTERVAL: "(0::real) <= (x::real) &
x <= (1::real) & (0::real) <= (y::real) & y <= (1::real)
==> abs (x - y) <= (1::real)"
  by (import prob_extra ABS_UNIT_INTERVAL)

lemma MEM_NIL: "(ALL x. ~ List.member l x) = (l = [])"
  by (import prob_extra MEM_NIL)

lemma MAP_MEM: "List.member (map (f::'a => 'b) (l::'a list)) (x::'b) =
(EX y::'a. List.member l y & x = f y)"
  by (import prob_extra MAP_MEM)

lemma MEM_NIL_MAP_CONS: "~ List.member (map (op # x) l) []"
  by (import prob_extra MEM_NIL_MAP_CONS)

lemma FILTER_TRUE: "[x<-l. True] = l"
  by (import prob_extra FILTER_TRUE)

lemma FILTER_FALSE: "[x<-l. False] = []"
  by (import prob_extra FILTER_FALSE)

lemma FILTER_MEM: "List.member (filter P l) x ==> P x"
  by (import prob_extra FILTER_MEM)

lemma MEM_FILTER: "List.member (filter P l) x ==> List.member l x"
  by (import prob_extra MEM_FILTER)

lemma FILTER_OUT_ELT: "List.member l x | [y<-l. y ~= x] = l"
  by (import prob_extra FILTER_OUT_ELT)

lemma IS_PREFIX_NIL: "IS_PREFIX x [] & IS_PREFIX [] x = (x = [])"
  by (import prob_extra IS_PREFIX_NIL)

lemma IS_PREFIX_REFL: "IS_PREFIX x x"
  by (import prob_extra IS_PREFIX_REFL)

lemma IS_PREFIX_ANTISYM: "IS_PREFIX y x & IS_PREFIX x y ==> x = y"
  by (import prob_extra IS_PREFIX_ANTISYM)

lemma IS_PREFIX_TRANS: "IS_PREFIX x y & IS_PREFIX y z ==> IS_PREFIX x z"
  by (import prob_extra IS_PREFIX_TRANS)

lemma IS_PREFIX_BUTLAST: "IS_PREFIX (x # y) (butlast (x # y))"
  by (import prob_extra IS_PREFIX_BUTLAST)

lemma IS_PREFIX_LENGTH: "IS_PREFIX y x ==> length x <= length y"
  by (import prob_extra IS_PREFIX_LENGTH)

lemma IS_PREFIX_LENGTH_ANTI: "IS_PREFIX y x & length x = length y ==> x = y"
  by (import prob_extra IS_PREFIX_LENGTH_ANTI)

lemma IS_PREFIX_SNOC: "IS_PREFIX (SNOC x y) z = (IS_PREFIX y z | z = SNOC x y)"
  by (import prob_extra IS_PREFIX_SNOC)

lemma FOLDR_MAP: "foldr (f::'b => 'c => 'c) (map (g::'a => 'b) (l::'a list)) (e::'c) =
foldr (%x::'a. f (g x)) l e"
  by (import prob_extra FOLDR_MAP)

lemma LAST_MEM: "List.member (h # t) (last (h # t))"
  by (import prob_extra LAST_MEM)

lemma LAST_MAP_CONS: "EX x::bool list.
   last (map (op # (b::bool)) ((h::bool list) # (t::bool list list))) =
   b # x"
  by (import prob_extra LAST_MAP_CONS)

lemma EXISTS_LONGEST: "EX z. List.member (x # y) z &
      (ALL w. List.member (x # y) w --> length w <= length z)"
  by (import prob_extra EXISTS_LONGEST)

lemma UNION_DEF_ALT: "pred_set.UNION s t = (%x. s x | t x)"
  by (import prob_extra UNION_DEF_ALT)

lemma INTER_UNION_RDISTRIB: "pred_set.INTER (pred_set.UNION p q) r =
pred_set.UNION (pred_set.INTER p r) (pred_set.INTER q r)"
  by (import prob_extra INTER_UNION_RDISTRIB)

lemma SUBSET_EQ: "(x = xa) = (SUBSET x xa & SUBSET xa x)"
  by (import prob_extra SUBSET_EQ)

lemma INTER_IS_EMPTY: "(pred_set.INTER s t = EMPTY) = (ALL x. ~ s x | ~ t x)"
  by (import prob_extra INTER_IS_EMPTY)

lemma UNION_DISJOINT_SPLIT: "pred_set.UNION s t = pred_set.UNION s u &
pred_set.INTER s t = EMPTY & pred_set.INTER s u = EMPTY
==> t = u"
  by (import prob_extra UNION_DISJOINT_SPLIT)

lemma GSPEC_DEF_ALT: "GSPEC (f::'a => 'b * bool) = (%v::'b. EX x::'a. (v, True) = f x)"
  by (import prob_extra GSPEC_DEF_ALT)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" prob_canon

consts
  alg_twin :: "bool list => bool list => bool" 

defs
  alg_twin_primdef: "alg_twin == %x y. EX l. x = SNOC True l & y = SNOC False l"

lemma alg_twin_def: "alg_twin x y = (EX l. x = SNOC True l & y = SNOC False l)"
  by (import prob_canon alg_twin_def)

definition
  alg_order_tupled :: "bool list * bool list => bool"  where
  "alg_order_tupled ==
WFREC (SOME R. WF R & (ALL h' h t' t. R (t, t') (h # t, h' # t')))
 (%alg_order_tupled (v, v1).
     case v of [] => case v1 of [] => True | _ => True
     | v4 # v5 =>
         case v1 of [] => False
         | v10 # v11 =>
             v4 = True & v10 = False |
             v4 = v10 & alg_order_tupled (v5, v11))"

lemma alg_order_tupled_primitive_def: "alg_order_tupled =
WFREC (SOME R. WF R & (ALL h' h t' t. R (t, t') (h # t, h' # t')))
 (%alg_order_tupled (v, v1).
     case v of [] => case v1 of [] => True | _ => True
     | v4 # v5 =>
         case v1 of [] => False
         | v10 # v11 =>
             v4 = True & v10 = False |
             v4 = v10 & alg_order_tupled (v5, v11))"
  by (import prob_canon alg_order_tupled_primitive_def)

consts
  alg_order :: "bool list => bool list => bool" 

defs
  alg_order_primdef: "alg_order == %x x1. alg_order_tupled (x, x1)"

lemma alg_order_curried_def: "alg_order x x1 = alg_order_tupled (x, x1)"
  by (import prob_canon alg_order_curried_def)

lemma alg_order_ind: "(ALL (x::bool) xa::bool list.
    (P::bool list => bool list => bool) [] (x # xa)) &
P [] [] &
(ALL (x::bool) xa::bool list. P (x # xa) []) &
(ALL (x::bool) (xa::bool list) (xb::bool) xc::bool list.
    P xa xc --> P (x # xa) (xb # xc))
==> P (x::bool list) (xa::bool list)"
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

lemma alg_sorted_ind: "(ALL (x::bool list) (y::bool list) z::bool list list.
    (P::bool list list => bool) (y # z) --> P (x # y # z)) &
(ALL v::bool list. P [v]) & P []
==> P (x::bool list list)"
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

lemma alg_prefixfree_ind: "(ALL (x::bool list) (y::bool list) z::bool list list.
    (P::bool list list => bool) (y # z) --> P (x # y # z)) &
(ALL v::bool list. P [v]) & P []
==> P (x::bool list list)"
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

lemma alg_twinfree_ind: "(ALL (x::bool list) (y::bool list) z::bool list list.
    (P::bool list list => bool) (y # z) --> P (x # y # z)) &
(ALL v::bool list. P [v]) & P []
==> P (x::bool list list)"
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

lemma alg_canon_def: "alg_canon l = alg_canon2 (alg_canon1 l)"
  by (import prob_canon alg_canon_def)

consts
  algebra_canon :: "bool list list => bool" 

defs
  algebra_canon_primdef: "algebra_canon == %l. alg_canon l = l"

lemma algebra_canon_def: "algebra_canon l = (alg_canon l = l)"
  by (import prob_canon algebra_canon_def)

lemma ALG_TWIN_NIL: "~ alg_twin l [] & ~ alg_twin [] l"
  by (import prob_canon ALG_TWIN_NIL)

lemma ALG_TWIN_SING: "alg_twin [x] l = (x = True & l = [False]) &
alg_twin l [x] = (l = [True] & x = False)"
  by (import prob_canon ALG_TWIN_SING)

lemma ALG_TWIN_CONS: "alg_twin (x # y # z) (h # t) = (x = h & alg_twin (y # z) t) &
alg_twin (h # t) (x # y # z) = (x = h & alg_twin t (y # z))"
  by (import prob_canon ALG_TWIN_CONS)

lemma ALG_TWIN_REDUCE: "alg_twin (h # t) (h # t') = alg_twin t t'"
  by (import prob_canon ALG_TWIN_REDUCE)

lemma ALG_TWINS_PREFIX: "IS_PREFIX x l
==> x = l | IS_PREFIX x (SNOC True l) | IS_PREFIX x (SNOC False l)"
  by (import prob_canon ALG_TWINS_PREFIX)

lemma ALG_ORDER_NIL: "alg_order [] x & alg_order x [] = (x = [])"
  by (import prob_canon ALG_ORDER_NIL)

lemma ALG_ORDER_REFL: "alg_order x x"
  by (import prob_canon ALG_ORDER_REFL)

lemma ALG_ORDER_ANTISYM: "alg_order x y & alg_order y x ==> x = y"
  by (import prob_canon ALG_ORDER_ANTISYM)

lemma ALG_ORDER_TRANS: "alg_order x y & alg_order y z ==> alg_order x z"
  by (import prob_canon ALG_ORDER_TRANS)

lemma ALG_ORDER_TOTAL: "alg_order x y | alg_order y x"
  by (import prob_canon ALG_ORDER_TOTAL)

lemma ALG_ORDER_PREFIX: "IS_PREFIX y x ==> alg_order x y"
  by (import prob_canon ALG_ORDER_PREFIX)

lemma ALG_ORDER_PREFIX_ANTI: "alg_order x y & IS_PREFIX x y ==> x = y"
  by (import prob_canon ALG_ORDER_PREFIX_ANTI)

lemma ALG_ORDER_PREFIX_MONO: "alg_order x y & alg_order y z & IS_PREFIX z x ==> IS_PREFIX y x"
  by (import prob_canon ALG_ORDER_PREFIX_MONO)

lemma ALG_ORDER_PREFIX_TRANS: "alg_order x y & IS_PREFIX y z ==> alg_order x z | IS_PREFIX x z"
  by (import prob_canon ALG_ORDER_PREFIX_TRANS)

lemma ALG_ORDER_SNOC: "~ alg_order (SNOC x l) l"
  by (import prob_canon ALG_ORDER_SNOC)

lemma ALG_SORTED_MIN: "[| alg_sorted (h # t); List.member t x |] ==> alg_order h x"
  by (import prob_canon ALG_SORTED_MIN)

lemma ALG_SORTED_DEF_ALT: "alg_sorted (h # t) =
((ALL x. List.member t x --> alg_order h x) & alg_sorted t)"
  by (import prob_canon ALG_SORTED_DEF_ALT)

lemma ALG_SORTED_TL: "alg_sorted (h # t) ==> alg_sorted t"
  by (import prob_canon ALG_SORTED_TL)

lemma ALG_SORTED_MONO: "alg_sorted (x # y # z) ==> alg_sorted (x # z)"
  by (import prob_canon ALG_SORTED_MONO)

lemma ALG_SORTED_TLS: "alg_sorted (map (op # b) l) = alg_sorted l"
  by (import prob_canon ALG_SORTED_TLS)

lemma ALG_SORTED_STEP: "alg_sorted (map (op # True) l1 @ map (op # False) l2) =
(alg_sorted l1 & alg_sorted l2)"
  by (import prob_canon ALG_SORTED_STEP)

lemma ALG_SORTED_APPEND: "alg_sorted ((h # t) @ h' # t') =
(alg_sorted (h # t) & alg_sorted (h' # t') & alg_order (last (h # t)) h')"
  by (import prob_canon ALG_SORTED_APPEND)

lemma ALG_SORTED_FILTER: "alg_sorted b ==> alg_sorted (filter P b)"
  by (import prob_canon ALG_SORTED_FILTER)

lemma ALG_PREFIXFREE_TL: "alg_prefixfree (h # t) ==> alg_prefixfree t"
  by (import prob_canon ALG_PREFIXFREE_TL)

lemma ALG_PREFIXFREE_MONO: "alg_sorted (x # y # z) & alg_prefixfree (x # y # z)
==> alg_prefixfree (x # z)"
  by (import prob_canon ALG_PREFIXFREE_MONO)

lemma ALG_PREFIXFREE_ELT: "[| alg_sorted (h # t) & alg_prefixfree (h # t); List.member t x |]
==> ~ IS_PREFIX x h & ~ IS_PREFIX h x"
  by (import prob_canon ALG_PREFIXFREE_ELT)

lemma ALG_PREFIXFREE_TLS: "alg_prefixfree (map (op # b) l) = alg_prefixfree l"
  by (import prob_canon ALG_PREFIXFREE_TLS)

lemma ALG_PREFIXFREE_STEP: "alg_prefixfree (map (op # True) l1 @ map (op # False) l2) =
(alg_prefixfree l1 & alg_prefixfree l2)"
  by (import prob_canon ALG_PREFIXFREE_STEP)

lemma ALG_PREFIXFREE_APPEND: "alg_prefixfree ((h # t) @ h' # t') =
(alg_prefixfree (h # t) &
 alg_prefixfree (h' # t') & ~ IS_PREFIX h' (last (h # t)))"
  by (import prob_canon ALG_PREFIXFREE_APPEND)

lemma ALG_PREFIXFREE_FILTER: "alg_sorted b & alg_prefixfree b ==> alg_prefixfree (filter P b)"
  by (import prob_canon ALG_PREFIXFREE_FILTER)

lemma ALG_TWINFREE_TL: "alg_twinfree (h # t) ==> alg_twinfree t"
  by (import prob_canon ALG_TWINFREE_TL)

lemma ALG_TWINFREE_TLS: "alg_twinfree (map (op # b) l) = alg_twinfree l"
  by (import prob_canon ALG_TWINFREE_TLS)

lemma ALG_TWINFREE_STEP1: "alg_twinfree (map (op # True) l1 @ map (op # False) l2)
==> alg_twinfree l1 & alg_twinfree l2"
  by (import prob_canon ALG_TWINFREE_STEP1)

lemma ALG_TWINFREE_STEP2: "(~ List.member l1 [] | ~ List.member l2 []) &
alg_twinfree l1 & alg_twinfree l2
==> alg_twinfree (map (op # True) l1 @ map (op # False) l2)"
  by (import prob_canon ALG_TWINFREE_STEP2)

lemma ALG_TWINFREE_STEP: "~ List.member l1 [] | ~ List.member l2 []
==> alg_twinfree (map (op # True) l1 @ map (op # False) l2) =
    (alg_twinfree l1 & alg_twinfree l2)"
  by (import prob_canon ALG_TWINFREE_STEP)

lemma ALG_LONGEST_HD: "length h <= alg_longest (h # t)"
  by (import prob_canon ALG_LONGEST_HD)

lemma ALG_LONGEST_TL: "alg_longest t <= alg_longest (h # t)"
  by (import prob_canon ALG_LONGEST_TL)

lemma ALG_LONGEST_TLS: "alg_longest (map (op # b) (h # t)) = Suc (alg_longest (h # t))"
  by (import prob_canon ALG_LONGEST_TLS)

lemma ALG_LONGEST_APPEND: "alg_longest l1 <= alg_longest (l1 @ l2) &
alg_longest l2 <= alg_longest (l1 @ l2)"
  by (import prob_canon ALG_LONGEST_APPEND)

lemma ALG_CANON_PREFS_HD: "hd (alg_canon_prefs l b) = l"
  by (import prob_canon ALG_CANON_PREFS_HD)

lemma ALG_CANON_PREFS_DELETES: "List.member (alg_canon_prefs l b) x ==> List.member (l # b) x"
  by (import prob_canon ALG_CANON_PREFS_DELETES)

lemma ALG_CANON_PREFS_SORTED: "alg_sorted (l # b) ==> alg_sorted (alg_canon_prefs l b)"
  by (import prob_canon ALG_CANON_PREFS_SORTED)

lemma ALG_CANON_PREFS_PREFIXFREE: "alg_sorted b & alg_prefixfree b ==> alg_prefixfree (alg_canon_prefs l b)"
  by (import prob_canon ALG_CANON_PREFS_PREFIXFREE)

lemma ALG_CANON_PREFS_CONSTANT: "alg_prefixfree (l # b) ==> alg_canon_prefs l b = l # b"
  by (import prob_canon ALG_CANON_PREFS_CONSTANT)

lemma ALG_CANON_FIND_HD: "hd (alg_canon_find l (h # t)) = l | hd (alg_canon_find l (h # t)) = h"
  by (import prob_canon ALG_CANON_FIND_HD)

lemma ALG_CANON_FIND_DELETES: "List.member (alg_canon_find l b) x ==> List.member (l # b) x"
  by (import prob_canon ALG_CANON_FIND_DELETES)

lemma ALG_CANON_FIND_SORTED: "alg_sorted b ==> alg_sorted (alg_canon_find l b)"
  by (import prob_canon ALG_CANON_FIND_SORTED)

lemma ALG_CANON_FIND_PREFIXFREE: "alg_sorted b & alg_prefixfree b ==> alg_prefixfree (alg_canon_find l b)"
  by (import prob_canon ALG_CANON_FIND_PREFIXFREE)

lemma ALG_CANON_FIND_CONSTANT: "alg_sorted (l # b) & alg_prefixfree (l # b) ==> alg_canon_find l b = l # b"
  by (import prob_canon ALG_CANON_FIND_CONSTANT)

lemma ALG_CANON1_SORTED: "alg_sorted (alg_canon1 x)"
  by (import prob_canon ALG_CANON1_SORTED)

lemma ALG_CANON1_PREFIXFREE: "alg_prefixfree (alg_canon1 l)"
  by (import prob_canon ALG_CANON1_PREFIXFREE)

lemma ALG_CANON1_CONSTANT: "alg_sorted l & alg_prefixfree l ==> alg_canon1 l = l"
  by (import prob_canon ALG_CANON1_CONSTANT)

lemma ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE: "alg_sorted (l # b) & alg_prefixfree (l # b) & alg_twinfree b
==> alg_sorted (alg_canon_merge l b) &
    alg_prefixfree (alg_canon_merge l b) &
    alg_twinfree (alg_canon_merge l b)"
  by (import prob_canon ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON_MERGE_PREFIXFREE_PRESERVE: "[| !!x. List.member (l # b) x ==> ~ IS_PREFIX h x & ~ IS_PREFIX x h;
   List.member (alg_canon_merge l b) x |]
==> ~ IS_PREFIX h x & ~ IS_PREFIX x h"
  by (import prob_canon ALG_CANON_MERGE_PREFIXFREE_PRESERVE)

lemma ALG_CANON_MERGE_SHORTENS: "List.member (alg_canon_merge l b) x
==> EX y. List.member (l # b) y & IS_PREFIX y x"
  by (import prob_canon ALG_CANON_MERGE_SHORTENS)

lemma ALG_CANON_MERGE_CONSTANT: "alg_twinfree (l # b) ==> alg_canon_merge l b = l # b"
  by (import prob_canon ALG_CANON_MERGE_CONSTANT)

lemma ALG_CANON2_PREFIXFREE_PRESERVE: "[| !!xb. List.member x xb ==> ~ IS_PREFIX xa xb & ~ IS_PREFIX xb xa;
   List.member (alg_canon2 x) xb |]
==> ~ IS_PREFIX xa xb & ~ IS_PREFIX xb xa"
  by (import prob_canon ALG_CANON2_PREFIXFREE_PRESERVE)

lemma ALG_CANON2_SHORTENS: "List.member (alg_canon2 x) xa ==> EX y. List.member x y & IS_PREFIX y xa"
  by (import prob_canon ALG_CANON2_SHORTENS)

lemma ALG_CANON2_SORTED_PREFIXFREE_TWINFREE: "alg_sorted x & alg_prefixfree x
==> alg_sorted (alg_canon2 x) &
    alg_prefixfree (alg_canon2 x) & alg_twinfree (alg_canon2 x)"
  by (import prob_canon ALG_CANON2_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON2_CONSTANT: "alg_twinfree l ==> alg_canon2 l = l"
  by (import prob_canon ALG_CANON2_CONSTANT)

lemma ALG_CANON_SORTED_PREFIXFREE_TWINFREE: "alg_sorted (alg_canon l) &
alg_prefixfree (alg_canon l) & alg_twinfree (alg_canon l)"
  by (import prob_canon ALG_CANON_SORTED_PREFIXFREE_TWINFREE)

lemma ALG_CANON_CONSTANT: "alg_sorted l & alg_prefixfree l & alg_twinfree l ==> alg_canon l = l"
  by (import prob_canon ALG_CANON_CONSTANT)

lemma ALG_CANON_IDEMPOT: "alg_canon (alg_canon l) = alg_canon l"
  by (import prob_canon ALG_CANON_IDEMPOT)

lemma ALGEBRA_CANON_DEF_ALT: "algebra_canon l = (alg_sorted l & alg_prefixfree l & alg_twinfree l)"
  by (import prob_canon ALGEBRA_CANON_DEF_ALT)

lemma ALGEBRA_CANON_BASIC: "algebra_canon [] & algebra_canon [[]] & (ALL x. algebra_canon [x])"
  by (import prob_canon ALGEBRA_CANON_BASIC)

lemma ALG_CANON_BASIC: "alg_canon [] = [] & alg_canon [[]] = [[]] & (ALL x. alg_canon [x] = [x])"
  by (import prob_canon ALG_CANON_BASIC)

lemma ALGEBRA_CANON_TL: "algebra_canon (h # t) ==> algebra_canon t"
  by (import prob_canon ALGEBRA_CANON_TL)

lemma ALGEBRA_CANON_NIL_MEM: "(algebra_canon l & List.member l []) = (l = [[]])"
  by (import prob_canon ALGEBRA_CANON_NIL_MEM)

lemma ALGEBRA_CANON_TLS: "algebra_canon (map (op # b) l) = algebra_canon l"
  by (import prob_canon ALGEBRA_CANON_TLS)

lemma ALGEBRA_CANON_STEP1: "algebra_canon (map (op # True) l1 @ map (op # False) l2)
==> algebra_canon l1 & algebra_canon l2"
  by (import prob_canon ALGEBRA_CANON_STEP1)

lemma ALGEBRA_CANON_STEP2: "(l1 ~= [[]] | l2 ~= [[]]) & algebra_canon l1 & algebra_canon l2
==> algebra_canon (map (op # True) l1 @ map (op # False) l2)"
  by (import prob_canon ALGEBRA_CANON_STEP2)

lemma ALGEBRA_CANON_STEP: "l1 ~= [[]] | l2 ~= [[]]
==> algebra_canon (map (op # True) l1 @ map (op # False) l2) =
    (algebra_canon l1 & algebra_canon l2)"
  by (import prob_canon ALGEBRA_CANON_STEP)

lemma ALGEBRA_CANON_CASES_THM: "algebra_canon l
==> l = [] |
    l = [[]] |
    (EX l1 l2.
        algebra_canon l1 &
        algebra_canon l2 & l = map (op # True) l1 @ map (op # False) l2)"
  by (import prob_canon ALGEBRA_CANON_CASES_THM)

lemma ALGEBRA_CANON_CASES: "[| P [] &
   P [[]] &
   (ALL l1 l2.
       algebra_canon l1 &
       algebra_canon l2 &
       algebra_canon (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2));
   algebra_canon l |]
==> P l"
  by (import prob_canon ALGEBRA_CANON_CASES)

lemma ALGEBRA_CANON_INDUCTION: "[| P [] &
   P [[]] &
   (ALL l1 l2.
       algebra_canon l1 &
       algebra_canon l2 &
       P l1 &
       P l2 & algebra_canon (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2));
   algebra_canon l |]
==> P l"
  by (import prob_canon ALGEBRA_CANON_INDUCTION)

lemma MEM_NIL_STEP: "~ List.member (map (op # True) l1 @ map (op # False) l2) []"
  by (import prob_canon MEM_NIL_STEP)

lemma ALG_SORTED_PREFIXFREE_MEM_NIL: "(alg_sorted l & alg_prefixfree l & List.member l []) = (l = [[]])"
  by (import prob_canon ALG_SORTED_PREFIXFREE_MEM_NIL)

lemma ALG_SORTED_PREFIXFREE_EQUALITY: "(ALL x. List.member l x = List.member l' x) &
alg_sorted l & alg_sorted l' & alg_prefixfree l & alg_prefixfree l'
==> l = l'"
  by (import prob_canon ALG_SORTED_PREFIXFREE_EQUALITY)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" boolean_sequence

consts
  SHD :: "(nat => bool) => bool" 

defs
  SHD_primdef: "SHD == %f. f 0"

lemma SHD_def: "SHD f = f 0"
  by (import boolean_sequence SHD_def)

consts
  STL :: "(nat => bool) => nat => bool" 

defs
  STL_primdef: "STL == %f n. f (Suc n)"

lemma STL_def: "STL f n = f (Suc n)"
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

lemma SCONS_SURJ: "EX xa t. x = SCONS xa t"
  by (import boolean_sequence SCONS_SURJ)

lemma SHD_STL_ISO: "EX x. SHD x = h & STL x = t"
  by (import boolean_sequence SHD_STL_ISO)

lemma SHD_SCONS: "SHD (SCONS h t) = h"
  by (import boolean_sequence SHD_SCONS)

lemma STL_SCONS: "STL (SCONS h t) = t"
  by (import boolean_sequence STL_SCONS)

lemma SHD_SCONST: "SHD (SCONST b) = b"
  by (import boolean_sequence SHD_SCONST)

lemma STL_SCONST: "STL (SCONST b) = SCONST b"
  by (import boolean_sequence STL_SCONST)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" prob_algebra

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

lemma measurable_def: "measurable s = (EX b. s = algebra_embed b)"
  by (import prob_algebra measurable_def)

lemma HALVES_INTER: "pred_set.INTER (%x. SHD x = True) (%x. SHD x = False) = EMPTY"
  by (import prob_algebra HALVES_INTER)

lemma INTER_STL: "pred_set.INTER p q o STL = pred_set.INTER (p o STL) (q o STL)"
  by (import prob_algebra INTER_STL)

lemma COMPL_SHD: "COMPL (%x. SHD x = b) = (%x. SHD x = (~ b))"
  by (import prob_algebra COMPL_SHD)

lemma ALG_EMBED_BASIC: "alg_embed [] = pred_set.UNIV &
(ALL h t.
    alg_embed (h # t) = pred_set.INTER (%x. SHD x = h) (alg_embed t o STL))"
  by (import prob_algebra ALG_EMBED_BASIC)

lemma ALG_EMBED_NIL: "All (alg_embed c) = (c = [])"
  by (import prob_algebra ALG_EMBED_NIL)

lemma ALG_EMBED_POPULATED: "Ex (alg_embed b)"
  by (import prob_algebra ALG_EMBED_POPULATED)

lemma ALG_EMBED_PREFIX: "alg_embed b s & alg_embed c s ==> IS_PREFIX b c | IS_PREFIX c b"
  by (import prob_algebra ALG_EMBED_PREFIX)

lemma ALG_EMBED_PREFIX_SUBSET: "SUBSET (alg_embed b) (alg_embed c) = IS_PREFIX b c"
  by (import prob_algebra ALG_EMBED_PREFIX_SUBSET)

lemma ALG_EMBED_TWINS: "pred_set.UNION (alg_embed (SNOC True l)) (alg_embed (SNOC False l)) =
alg_embed l"
  by (import prob_algebra ALG_EMBED_TWINS)

lemma ALGEBRA_EMBED_BASIC: "algebra_embed [] = EMPTY &
algebra_embed [[]] = pred_set.UNIV &
(ALL b. algebra_embed [[b]] = (%s. SHD s = b))"
  by (import prob_algebra ALGEBRA_EMBED_BASIC)

lemma ALGEBRA_EMBED_MEM: "algebra_embed b x ==> EX l. List.member b l & alg_embed l x"
  by (import prob_algebra ALGEBRA_EMBED_MEM)

lemma ALGEBRA_EMBED_APPEND: "algebra_embed (l1 @ l2) =
pred_set.UNION (algebra_embed l1) (algebra_embed l2)"
  by (import prob_algebra ALGEBRA_EMBED_APPEND)

lemma ALGEBRA_EMBED_TLS: "algebra_embed (map (op # b) l) (SCONS h t) = (h = b & algebra_embed l t)"
  by (import prob_algebra ALGEBRA_EMBED_TLS)

lemma ALG_CANON_PREFS_EMBED: "algebra_embed (alg_canon_prefs l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_PREFS_EMBED)

lemma ALG_CANON_FIND_EMBED: "algebra_embed (alg_canon_find l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_FIND_EMBED)

lemma ALG_CANON1_EMBED: "algebra_embed (alg_canon1 x) = algebra_embed x"
  by (import prob_algebra ALG_CANON1_EMBED)

lemma ALG_CANON_MERGE_EMBED: "algebra_embed (alg_canon_merge l b) = algebra_embed (l # b)"
  by (import prob_algebra ALG_CANON_MERGE_EMBED)

lemma ALG_CANON2_EMBED: "algebra_embed (alg_canon2 x) = algebra_embed x"
  by (import prob_algebra ALG_CANON2_EMBED)

lemma ALG_CANON_EMBED: "algebra_embed (alg_canon l) = algebra_embed l"
  by (import prob_algebra ALG_CANON_EMBED)

lemma ALGEBRA_CANON_UNIV: "[| algebra_canon l; algebra_embed l = pred_set.UNIV |] ==> l = [[]]"
  by (import prob_algebra ALGEBRA_CANON_UNIV)

lemma ALG_CANON_REP: "(alg_canon b = alg_canon c) = (algebra_embed b = algebra_embed c)"
  by (import prob_algebra ALG_CANON_REP)

lemma ALGEBRA_CANON_EMBED_EMPTY: "algebra_canon l ==> (ALL v. ~ algebra_embed l v) = (l = [])"
  by (import prob_algebra ALGEBRA_CANON_EMBED_EMPTY)

lemma ALGEBRA_CANON_EMBED_UNIV: "algebra_canon l ==> All (algebra_embed l) = (l = [[]])"
  by (import prob_algebra ALGEBRA_CANON_EMBED_UNIV)

lemma MEASURABLE_ALGEBRA: "measurable (algebra_embed b)"
  by (import prob_algebra MEASURABLE_ALGEBRA)

lemma MEASURABLE_BASIC: "measurable EMPTY &
measurable pred_set.UNIV & (ALL b. measurable (%s. SHD s = b))"
  by (import prob_algebra MEASURABLE_BASIC)

lemma MEASURABLE_SHD: "measurable (%s. SHD s = b)"
  by (import prob_algebra MEASURABLE_SHD)

lemma ALGEBRA_EMBED_COMPL: "EX l'. COMPL (algebra_embed l) = algebra_embed l'"
  by (import prob_algebra ALGEBRA_EMBED_COMPL)

lemma MEASURABLE_COMPL: "measurable (COMPL s) = measurable s"
  by (import prob_algebra MEASURABLE_COMPL)

lemma MEASURABLE_UNION: "measurable s & measurable t ==> measurable (pred_set.UNION s t)"
  by (import prob_algebra MEASURABLE_UNION)

lemma MEASURABLE_INTER: "measurable s & measurable t ==> measurable (pred_set.INTER s t)"
  by (import prob_algebra MEASURABLE_INTER)

lemma MEASURABLE_STL: "measurable (p o STL) = measurable p"
  by (import prob_algebra MEASURABLE_STL)

lemma MEASURABLE_SDROP: "measurable (p o SDROP n) = measurable p"
  by (import prob_algebra MEASURABLE_SDROP)

lemma MEASURABLE_INTER_HALVES: "(measurable (pred_set.INTER (%x. SHD x = True) p) &
 measurable (pred_set.INTER (%x. SHD x = False) p)) =
measurable p"
  by (import prob_algebra MEASURABLE_INTER_HALVES)

lemma MEASURABLE_HALVES: "measurable
 (pred_set.UNION (pred_set.INTER (%x. SHD x = True) p)
   (pred_set.INTER (%x. SHD x = False) q)) =
(measurable (pred_set.INTER (%x. SHD x = True) p) &
 measurable (pred_set.INTER (%x. SHD x = False) q))"
  by (import prob_algebra MEASURABLE_HALVES)

lemma MEASURABLE_INTER_SHD: "measurable (pred_set.INTER (%x. SHD x = b) (p o STL)) = measurable p"
  by (import prob_algebra MEASURABLE_INTER_SHD)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" prob

consts
  alg_measure :: "bool list list => real" 

specification (alg_measure_primdef: alg_measure) alg_measure_def: "alg_measure [] = 0 &
(ALL l rest. alg_measure (l # rest) = (1 / 2) ^ length l + alg_measure rest)"
  by (import prob alg_measure_def)

consts
  algebra_measure :: "bool list list => real" 

defs
  algebra_measure_primdef: "algebra_measure ==
%b. prob_extra.inf
     (%r. EX c. algebra_embed b = algebra_embed c & alg_measure c = r)"

lemma algebra_measure_def: "algebra_measure b =
prob_extra.inf
 (%r. EX c. algebra_embed b = algebra_embed c & alg_measure c = r)"
  by (import prob algebra_measure_def)

consts
  prob :: "((nat => bool) => bool) => real" 

defs
  prob_primdef: "prob ==
%s. real.sup (%r. EX b. algebra_measure b = r & SUBSET (algebra_embed b) s)"

lemma prob_def: "prob s =
real.sup (%r. EX b. algebra_measure b = r & SUBSET (algebra_embed b) s)"
  by (import prob prob_def)

lemma ALG_TWINS_MEASURE: "((1::real) / (2::real)) ^ length (SNOC True (l::bool list)) +
((1::real) / (2::real)) ^ length (SNOC False l) =
((1::real) / (2::real)) ^ length l"
  by (import prob ALG_TWINS_MEASURE)

lemma ALG_MEASURE_BASIC: "alg_measure [] = 0 &
alg_measure [[]] = 1 & (ALL b. alg_measure [[b]] = 1 / 2)"
  by (import prob ALG_MEASURE_BASIC)

lemma ALG_MEASURE_POS: "0 <= alg_measure l"
  by (import prob ALG_MEASURE_POS)

lemma ALG_MEASURE_APPEND: "alg_measure (l1 @ l2) = alg_measure l1 + alg_measure l2"
  by (import prob ALG_MEASURE_APPEND)

lemma ALG_MEASURE_TLS: "2 * alg_measure (map (op # b) l) = alg_measure l"
  by (import prob ALG_MEASURE_TLS)

lemma ALG_CANON_PREFS_MONO: "alg_measure (alg_canon_prefs l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_PREFS_MONO)

lemma ALG_CANON_FIND_MONO: "alg_measure (alg_canon_find l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_FIND_MONO)

lemma ALG_CANON1_MONO: "alg_measure (alg_canon1 x) <= alg_measure x"
  by (import prob ALG_CANON1_MONO)

lemma ALG_CANON_MERGE_MONO: "alg_measure (alg_canon_merge l b) <= alg_measure (l # b)"
  by (import prob ALG_CANON_MERGE_MONO)

lemma ALG_CANON2_MONO: "alg_measure (alg_canon2 x) <= alg_measure x"
  by (import prob ALG_CANON2_MONO)

lemma ALG_CANON_MONO: "alg_measure (alg_canon l) <= alg_measure l"
  by (import prob ALG_CANON_MONO)

lemma ALGEBRA_MEASURE_DEF_ALT: "algebra_measure l = alg_measure (alg_canon l)"
  by (import prob ALGEBRA_MEASURE_DEF_ALT)

lemma ALGEBRA_MEASURE_BASIC: "algebra_measure [] = 0 &
algebra_measure [[]] = 1 & (ALL b. algebra_measure [[b]] = 1 / 2)"
  by (import prob ALGEBRA_MEASURE_BASIC)

lemma ALGEBRA_CANON_MEASURE_MAX: "algebra_canon l ==> alg_measure l <= 1"
  by (import prob ALGEBRA_CANON_MEASURE_MAX)

lemma ALGEBRA_MEASURE_MAX: "algebra_measure l <= 1"
  by (import prob ALGEBRA_MEASURE_MAX)

lemma ALGEBRA_MEASURE_MONO_EMBED: "SUBSET (algebra_embed x) (algebra_embed xa)
==> algebra_measure x <= algebra_measure xa"
  by (import prob ALGEBRA_MEASURE_MONO_EMBED)

lemma ALG_MEASURE_COMPL: "[| algebra_canon l; algebra_canon c;
   COMPL (algebra_embed l) = algebra_embed c |]
==> alg_measure l + alg_measure c = 1"
  by (import prob ALG_MEASURE_COMPL)

lemma ALG_MEASURE_ADDITIVE: "[| algebra_canon l; algebra_canon c; algebra_canon d;
   pred_set.INTER (algebra_embed c) (algebra_embed d) = EMPTY &
   algebra_embed l = pred_set.UNION (algebra_embed c) (algebra_embed d) |]
==> alg_measure l = alg_measure c + alg_measure d"
  by (import prob ALG_MEASURE_ADDITIVE)

lemma PROB_ALGEBRA: "prob (algebra_embed l) = algebra_measure l"
  by (import prob PROB_ALGEBRA)

lemma PROB_BASIC: "prob EMPTY = 0 &
prob pred_set.UNIV = 1 & (ALL b. prob (%s. SHD s = b) = 1 / 2)"
  by (import prob PROB_BASIC)

lemma PROB_ADDITIVE: "measurable s & measurable t & pred_set.INTER s t = EMPTY
==> prob (pred_set.UNION s t) = prob s + prob t"
  by (import prob PROB_ADDITIVE)

lemma PROB_COMPL: "measurable s ==> prob (COMPL s) = 1 - prob s"
  by (import prob PROB_COMPL)

lemma PROB_SUP_EXISTS1: "EX x b. algebra_measure b = x & SUBSET (algebra_embed b) s"
  by (import prob PROB_SUP_EXISTS1)

lemma PROB_SUP_EXISTS2: "EX x. ALL r.
         (EX b. algebra_measure b = r & SUBSET (algebra_embed b) s) -->
         r <= x"
  by (import prob PROB_SUP_EXISTS2)

lemma PROB_LE_X: "(!!s'. measurable s' & SUBSET s' s ==> prob s' <= x) ==> prob s <= x"
  by (import prob PROB_LE_X)

lemma X_LE_PROB: "EX s'. measurable s' & SUBSET s' s & x <= prob s' ==> x <= prob s"
  by (import prob X_LE_PROB)

lemma PROB_SUBSET_MONO: "SUBSET s t ==> prob s <= prob t"
  by (import prob PROB_SUBSET_MONO)

lemma PROB_ALG: "prob (alg_embed x) = (1 / 2) ^ length x"
  by (import prob PROB_ALG)

lemma PROB_STL: "measurable p ==> prob (p o STL) = prob p"
  by (import prob PROB_STL)

lemma PROB_SDROP: "measurable p ==> prob (p o SDROP n) = prob p"
  by (import prob PROB_SDROP)

lemma PROB_INTER_HALVES: "measurable p
==> prob (pred_set.INTER (%x. SHD x = True) p) +
    prob (pred_set.INTER (%x. SHD x = False) p) =
    prob p"
  by (import prob PROB_INTER_HALVES)

lemma PROB_INTER_SHD: "measurable p
==> prob (pred_set.INTER (%x. SHD x = b) (p o STL)) = 1 / 2 * prob p"
  by (import prob PROB_INTER_SHD)

lemma ALGEBRA_MEASURE_POS: "0 <= algebra_measure l"
  by (import prob ALGEBRA_MEASURE_POS)

lemma ALGEBRA_MEASURE_RANGE: "0 <= algebra_measure l & algebra_measure l <= 1"
  by (import prob ALGEBRA_MEASURE_RANGE)

lemma PROB_POS: "0 <= prob p"
  by (import prob PROB_POS)

lemma PROB_MAX: "prob p <= 1"
  by (import prob PROB_MAX)

lemma PROB_RANGE: "0 <= prob p & prob p <= 1"
  by (import prob PROB_RANGE)

lemma ABS_PROB: "abs (prob p) = prob p"
  by (import prob ABS_PROB)

lemma PROB_SHD: "prob (%s. SHD s = b) = 1 / 2"
  by (import prob PROB_SHD)

lemma PROB_COMPL_LE1: "measurable p ==> (prob (COMPL p) <= r) = (1 - r <= prob p)"
  by (import prob PROB_COMPL_LE1)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" prob_pseudo

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

lemma pseudo_linear_tl_def: "pseudo_linear_tl a b n x = (a * x + b) mod (2 * n + 1)"
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

setup_theory "~~/src/HOL/Import/HOL" prob_indep

consts
  indep_set :: "((nat => bool) => bool) => ((nat => bool) => bool) => bool" 

defs
  indep_set_primdef: "indep_set ==
%p q. measurable p &
      measurable q & prob (pred_set.INTER p q) = prob p * prob q"

lemma indep_set_def: "indep_set p q =
(measurable p & measurable q & prob (pred_set.INTER p q) = prob p * prob q)"
  by (import prob_indep indep_set_def)

consts
  alg_cover_set :: "bool list list => bool" 

defs
  alg_cover_set_primdef: "alg_cover_set ==
%l. alg_sorted l & alg_prefixfree l & algebra_embed l = pred_set.UNIV"

lemma alg_cover_set_def: "alg_cover_set l =
(alg_sorted l & alg_prefixfree l & algebra_embed l = pred_set.UNIV)"
  by (import prob_indep alg_cover_set_def)

consts
  alg_cover :: "bool list list => (nat => bool) => bool list" 

defs
  alg_cover_primdef: "alg_cover == %l x. SOME b. List.member l b & alg_embed b x"

lemma alg_cover_def: "alg_cover l x = (SOME b. List.member l b & alg_embed b x)"
  by (import prob_indep alg_cover_def)

consts
  indep :: "((nat => bool) => 'a * (nat => bool)) => bool" 

defs
  indep_primdef: "indep ==
%f. EX l r.
       alg_cover_set l &
       (ALL s. f s = (let c = alg_cover l s in (r c, SDROP (length c) s)))"

lemma indep_def: "indep f =
(EX l r.
    alg_cover_set l &
    (ALL s. f s = (let c = alg_cover l s in (r c, SDROP (length c) s))))"
  by (import prob_indep indep_def)

lemma INDEP_SET_BASIC: "measurable p ==> indep_set EMPTY p & indep_set pred_set.UNIV p"
  by (import prob_indep INDEP_SET_BASIC)

lemma INDEP_SET_SYM: "indep_set p q = indep_set p q"
  by (import prob_indep INDEP_SET_SYM)

lemma INDEP_SET_DISJOINT_DECOMP: "indep_set p r & indep_set q r & pred_set.INTER p q = EMPTY
==> indep_set (pred_set.UNION p q) r"
  by (import prob_indep INDEP_SET_DISJOINT_DECOMP)

lemma ALG_COVER_SET_BASIC: "~ alg_cover_set [] & alg_cover_set [[]] & alg_cover_set [[True], [False]]"
  by (import prob_indep ALG_COVER_SET_BASIC)

lemma ALG_COVER_WELL_DEFINED: "alg_cover_set l
==> List.member l (alg_cover l x) & alg_embed (alg_cover l x) x"
  by (import prob_indep ALG_COVER_WELL_DEFINED)

lemma ALG_COVER_UNIV: "alg_cover [[]] = K []"
  by (import prob_indep ALG_COVER_UNIV)

lemma MAP_CONS_TL_FILTER: "~ List.member (l::bool list list) []
==> map (op # (b::bool)) (map tl [x::bool list<-l. hd x = b]) =
    [x::bool list<-l. hd x = b]"
  by (import prob_indep MAP_CONS_TL_FILTER)

lemma ALG_COVER_SET_CASES_THM: "alg_cover_set l =
(l = [[]] |
 (EX x xa.
     alg_cover_set x &
     alg_cover_set xa & l = map (op # True) x @ map (op # False) xa))"
  by (import prob_indep ALG_COVER_SET_CASES_THM)

lemma ALG_COVER_SET_CASES: "[| P [[]] &
   (ALL l1 l2.
       alg_cover_set l1 &
       alg_cover_set l2 &
       alg_cover_set (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2));
   alg_cover_set l |]
==> P l"
  by (import prob_indep ALG_COVER_SET_CASES)

lemma ALG_COVER_SET_INDUCTION: "[| P [[]] &
   (ALL l1 l2.
       alg_cover_set l1 &
       alg_cover_set l2 &
       P l1 &
       P l2 & alg_cover_set (map (op # True) l1 @ map (op # False) l2) -->
       P (map (op # True) l1 @ map (op # False) l2));
   alg_cover_set l |]
==> P l"
  by (import prob_indep ALG_COVER_SET_INDUCTION)

lemma ALG_COVER_EXISTS_UNIQUE: "alg_cover_set l ==> EX! x. List.member l x & alg_embed x s"
  by (import prob_indep ALG_COVER_EXISTS_UNIQUE)

lemma ALG_COVER_UNIQUE: "alg_cover_set l & List.member l x & alg_embed x s ==> alg_cover l s = x"
  by (import prob_indep ALG_COVER_UNIQUE)

lemma ALG_COVER_STEP: "alg_cover_set l1 & alg_cover_set l2
==> alg_cover (map (op # True) l1 @ map (op # False) l2) (SCONS h t) =
    (if h then True # alg_cover l1 t else False # alg_cover l2 t)"
  by (import prob_indep ALG_COVER_STEP)

lemma ALG_COVER_HEAD: "alg_cover_set l ==> f o alg_cover l = algebra_embed (filter f l)"
  by (import prob_indep ALG_COVER_HEAD)

lemma ALG_COVER_TAIL_STEP: "alg_cover_set l1 & alg_cover_set l2
==> q o
    (%x. SDROP
          (length (alg_cover (map (op # True) l1 @ map (op # False) l2) x))
          x) =
    pred_set.UNION
     (pred_set.INTER (%x. SHD x = True)
       (q o ((%x. SDROP (length (alg_cover l1 x)) x) o STL)))
     (pred_set.INTER (%x. SHD x = False)
       (q o ((%x. SDROP (length (alg_cover l2 x)) x) o STL)))"
  by (import prob_indep ALG_COVER_TAIL_STEP)

lemma ALG_COVER_TAIL_MEASURABLE: "alg_cover_set l
==> measurable (q o (%x. SDROP (length (alg_cover l x)) x)) = measurable q"
  by (import prob_indep ALG_COVER_TAIL_MEASURABLE)

lemma ALG_COVER_TAIL_PROB: "[| alg_cover_set l; measurable q |]
==> prob (q o (%x. SDROP (length (alg_cover l x)) x)) = prob q"
  by (import prob_indep ALG_COVER_TAIL_PROB)

lemma INDEP_INDEP_SET_LEMMA: "[| alg_cover_set l; measurable q; List.member l x |]
==> prob
     (pred_set.INTER (alg_embed x)
       (q o (%x. SDROP (length (alg_cover l x)) x))) =
    (1 / 2) ^ length x * prob q"
  by (import prob_indep INDEP_INDEP_SET_LEMMA)

lemma INDEP_SET_LIST: "alg_sorted l &
alg_prefixfree l &
measurable q & (ALL x. List.member l x --> indep_set (alg_embed x) q)
==> indep_set (algebra_embed l) q"
  by (import prob_indep INDEP_SET_LIST)

lemma INDEP_INDEP_SET: "indep f & measurable q ==> indep_set (p o (fst o f)) (q o (snd o f))"
  by (import prob_indep INDEP_INDEP_SET)

lemma INDEP_UNIT: "indep (UNIT x)"
  by (import prob_indep INDEP_UNIT)

lemma INDEP_SDEST: "indep SDEST"
  by (import prob_indep INDEP_SDEST)

lemma BIND_STEP: "BIND SDEST (%k. f o SCONS k) = f"
  by (import prob_indep BIND_STEP)

lemma INDEP_BIND_SDEST: "(!!x. indep (f x)) ==> indep (BIND SDEST f)"
  by (import prob_indep INDEP_BIND_SDEST)

lemma INDEP_BIND: "indep f & (ALL x. indep (g x)) ==> indep (BIND f g)"
  by (import prob_indep INDEP_BIND)

lemma INDEP_PROB: "indep f & measurable q
==> prob (pred_set.INTER (p o (fst o f)) (q o (snd o f))) =
    prob (p o (fst o f)) * prob q"
  by (import prob_indep INDEP_PROB)

lemma INDEP_MEASURABLE1: "indep f ==> measurable (p o (fst o f))"
  by (import prob_indep INDEP_MEASURABLE1)

lemma INDEP_MEASURABLE2: "indep f & measurable q ==> measurable (q o (snd o f))"
  by (import prob_indep INDEP_MEASURABLE2)

lemma PROB_INDEP_BOUND: "indep f
==> prob (%s. fst (f s) < Suc n) =
    prob (%s. fst (f s) < n) + prob (%s. fst (f s) = n)"
  by (import prob_indep PROB_INDEP_BOUND)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" prob_uniform

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

lemma unif_bound_ind: "P 0 & (ALL v. P (Suc v div 2) --> P (Suc v)) ==> P x"
  by (import prob_uniform unif_bound_ind)

definition
  unif_tupled :: "nat * (nat => bool) => nat * (nat => bool)"  where
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

lemma unif_curried_def: "unif x x1 = unif_tupled (x, x1)"
  by (import prob_uniform unif_curried_def)

lemma unif_def: "unif 0 s = (0, s) &
unif (Suc v2) s =
(let (m, s') = unif (Suc v2 div 2) s
 in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))"
  by (import prob_uniform unif_def)

lemma unif_ind: "All ((P::nat => (nat => bool) => bool) (0::nat)) &
(ALL (v2::nat) s::nat => bool. P (Suc v2 div (2::nat)) s --> P (Suc v2) s)
==> P (v::nat) (x::nat => bool)"
  by (import prob_uniform unif_ind)

definition
  uniform_tupled :: "nat * nat * (nat => bool) => nat * (nat => bool)"  where
  "uniform_tupled ==
WFREC
 (SOME R.
     WF R &
     (ALL t s n res s'.
         (res, s') = unif n s & ~ res < Suc n -->
         R (t, Suc n, s') (Suc t, Suc n, s)))
 (%uniform_tupled (v, v1).
     case v of 0 => case v1 of (0, v4) => ARB | (Suc v5, v4) => (0, v4)
     | Suc v2 =>
         case v1 of (0, v8) => ARB
         | (Suc v9, v8) =>
             let (res, s') = unif v9 v8
             in if res < Suc v9 then (res, s')
                else uniform_tupled (v2, Suc v9, s'))"

lemma uniform_tupled_primitive_def: "uniform_tupled =
WFREC
 (SOME R.
     WF R &
     (ALL t s n res s'.
         (res, s') = unif n s & ~ res < Suc n -->
         R (t, Suc n, s') (Suc t, Suc n, s)))
 (%uniform_tupled (v, v1).
     case v of 0 => case v1 of (0, v4) => ARB | (Suc v5, v4) => (0, v4)
     | Suc v2 =>
         case v1 of (0, v8) => ARB
         | (Suc v9, v8) =>
             let (res, s') = unif v9 v8
             in if res < Suc v9 then (res, s')
                else uniform_tupled (v2, Suc v9, s'))"
  by (import prob_uniform uniform_tupled_primitive_def)

consts
  uniform :: "nat => nat => (nat => bool) => nat * (nat => bool)" 

defs
  uniform_primdef: "uniform == %x x1 x2. uniform_tupled (x, x1, x2)"

lemma uniform_curried_def: "uniform x x1 x2 = uniform_tupled (x, x1, x2)"
  by (import prob_uniform uniform_curried_def)

lemma uniform_ind: "(ALL x. All (P (Suc x) 0)) &
All (P 0 0) &
(ALL x. All (P 0 (Suc x))) &
(ALL x xa xb.
    (ALL xc xd.
        (xc, xd) = unif xa xb & ~ xc < Suc xa --> P x (Suc xa) xd) -->
    P (Suc x) (Suc xa) xb)
==> P x xa xb"
  by (import prob_uniform uniform_ind)

lemma uniform_def: "uniform 0 (Suc n) s = (0, s) &
uniform (Suc t) (Suc n) s =
(let (xa, x) = unif n s
 in if xa < Suc n then (xa, x) else uniform t (Suc n) x)"
  by (import prob_uniform uniform_def)

lemma SUC_DIV_TWO_ZERO: "(Suc n div 2 = 0) = (n = 0)"
  by (import prob_uniform SUC_DIV_TWO_ZERO)

lemma UNIF_BOUND_LOWER: "n < 2 ^ unif_bound n"
  by (import prob_uniform UNIF_BOUND_LOWER)

lemma UNIF_BOUND_LOWER_SUC: "Suc n <= 2 ^ unif_bound n"
  by (import prob_uniform UNIF_BOUND_LOWER_SUC)

lemma UNIF_BOUND_UPPER: "n ~= 0 ==> 2 ^ unif_bound n <= 2 * n"
  by (import prob_uniform UNIF_BOUND_UPPER)

lemma UNIF_BOUND_UPPER_SUC: "2 ^ unif_bound n <= Suc (2 * n)"
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

lemma INDEP_UNIF: "indep (unif n)"
  by (import prob_uniform INDEP_UNIF)

lemma INDEP_UNIFORM: "indep (uniform t (Suc n))"
  by (import prob_uniform INDEP_UNIFORM)

lemma PROB_UNIF: "prob (%s. fst (unif n s) = k) =
(if k < 2 ^ unif_bound n then (1 / 2) ^ unif_bound n else 0)"
  by (import prob_uniform PROB_UNIF)

lemma UNIF_RANGE: "fst (unif n s) < 2 ^ unif_bound n"
  by (import prob_uniform UNIF_RANGE)

lemma PROB_UNIF_PAIR: "(prob (%s. fst (unif n s) = k) = prob (%s. fst (unif n s) = k')) =
((k < 2 ^ unif_bound n) = (k' < 2 ^ unif_bound n))"
  by (import prob_uniform PROB_UNIF_PAIR)

lemma PROB_UNIF_BOUND: "k <= 2 ^ unif_bound n
==> prob (%s. fst (unif n s) < k) = real k * (1 / 2) ^ unif_bound n"
  by (import prob_uniform PROB_UNIF_BOUND)

lemma PROB_UNIF_GOOD: "1 / 2 <= prob (%s. fst (unif n s) < Suc n)"
  by (import prob_uniform PROB_UNIF_GOOD)

lemma UNIFORM_RANGE: "fst (uniform t (Suc n) s) < Suc n"
  by (import prob_uniform UNIFORM_RANGE)

lemma PROB_UNIFORM_LOWER_BOUND: "[| !!k. k < Suc n ==> prob (%s. fst (uniform t (Suc n) s) = k) < b;
   m < Suc n |]
==> prob (%s. fst (uniform t (Suc n) s) < Suc m) < real (Suc m) * b"
  by (import prob_uniform PROB_UNIFORM_LOWER_BOUND)

lemma PROB_UNIFORM_UPPER_BOUND: "[| !!k. k < Suc n ==> b < prob (%s. fst (uniform t (Suc n) s) = k);
   m < Suc n |]
==> real (Suc m) * b < prob (%s. fst (uniform t (Suc n) s) < Suc m)"
  by (import prob_uniform PROB_UNIFORM_UPPER_BOUND)

lemma PROB_UNIFORM_PAIR_SUC: "k < Suc n & k' < Suc n
==> abs (prob (%s. fst (uniform t (Suc n) s) = k) -
         prob (%s. fst (uniform t (Suc n) s) = k'))
    <= (1 / 2) ^ t"
  by (import prob_uniform PROB_UNIFORM_PAIR_SUC)

lemma PROB_UNIFORM_SUC: "k < Suc n
==> abs (prob (%s. fst (uniform t (Suc n) s) = k) - 1 / real (Suc n))
    <= (1 / 2) ^ t"
  by (import prob_uniform PROB_UNIFORM_SUC)

lemma PROB_UNIFORM: "k < n
==> abs (prob (%s. fst (uniform t n s) = k) - 1 / real n) <= (1 / 2) ^ t"
  by (import prob_uniform PROB_UNIFORM)

;end_setup

end

