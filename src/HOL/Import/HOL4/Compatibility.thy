(*  Title:      HOL/Import/HOL4/Compatibility.thy
    Author:     Sebastian Skalberg (TU Muenchen)
*)

theory Compatibility
imports
  Complex_Main
  "~~/src/HOL/Old_Number_Theory/Primes"
  "~~/src/HOL/Library/ContNotDenum"
  "~~/src/HOL/Import/Importer"
begin

abbreviation (input) mem (infixl "mem" 55) where "x mem xs \<equiv> List.member xs x"
no_notation differentiable (infixl "differentiable" 60)
no_notation sums (infixr "sums" 80)

lemma EXISTS_UNIQUE_DEF: "(Ex1 P) = (Ex P & (ALL x y. P x & P y --> (x = y)))"
  by auto

lemma COND_DEF:"(If b t f) = (@x. ((b = True) --> (x = t)) & ((b = False) --> (x = f)))"
  by auto

definition LET :: "['a \<Rightarrow> 'b,'a] \<Rightarrow> 'b" where
  "LET f s == f s"

lemma [import_rew]: "LET f s = Let s f"
  by (simp add: LET_def Let_def)

lemmas [import_rew] = ONE_ONE_rew

lemma bool_case_DEF: "(bool_case x y b) = (if b then x else y)"
  by simp

lemma INR_INL_11: "(ALL y x. (Inl x = Inl y) = (x = y)) & (ALL y x. (Inr x = Inr y) = (x = y))"
  by safe

(*lemma INL_neq_INR: "ALL v1 v2. Sum_Type.Inr v2 ~= Sum_Type.Inl v1"
  by simp*)

primrec ISL :: "'a + 'b => bool" where
  "ISL (Inl x) = True"
| "ISL (Inr x) = False"

primrec ISR :: "'a + 'b => bool" where
  "ISR (Inl x) = False"
| "ISR (Inr x) = True"

lemma ISL: "(ALL x. ISL (Inl x)) & (ALL y. ~ISL (Inr y))"
  by simp

lemma ISR: "(ALL x. ISR (Inr x)) & (ALL y. ~ISR (Inl y))"
  by simp

primrec OUTL :: "'a + 'b => 'a" where
  "OUTL (Inl x) = x"

primrec OUTR :: "'a + 'b => 'b" where
  "OUTR (Inr x) = x"

lemma OUTL: "OUTL (Inl x) = x"
  by simp

lemma OUTR: "OUTR (Inr x) = x"
  by simp

lemma sum_axiom: "EX! h. h o Inl = f & h o Inr = g"
  apply (intro allI ex1I[of _ "sum_case f g"] conjI)
  apply (simp_all add: o_def fun_eq_iff)
  apply (rule)
  apply (induct_tac x)
  apply simp_all
  done

lemma sum_case_def: "(ALL f g x. sum_case f g (Inl x) = f x) & (ALL f g y. sum_case f g (Inr y) = g y)"
  by simp

lemma one: "ALL v. v = ()"
  by simp

lemma option_case_def: "(!u f. option_case u f None = u) & (!u f x. option_case u f (Some x) = f x)"
  by simp

lemma OPTION_MAP_DEF: "(!f x. Option.map f (Some x) = Some (f x)) & (!f. Option.map f None = None)"
  by simp

primrec IS_SOME :: "'a option => bool" where
  "IS_SOME (Some x) = True"
| "IS_SOME None = False"

primrec IS_NONE :: "'a option => bool" where
  "IS_NONE (Some x) = False"
| "IS_NONE None = True"

lemma IS_NONE_DEF: "(!x. IS_NONE (Some x) = False) & (IS_NONE None = True)"
  by simp

lemma IS_SOME_DEF: "(!x. IS_SOME (Some x) = True) & (IS_SOME None = False)"
  by simp

primrec OPTION_JOIN :: "'a option option => 'a option" where
  "OPTION_JOIN None = None"
| "OPTION_JOIN (Some x) = x"

lemma OPTION_JOIN_DEF: "(OPTION_JOIN None = None) & (ALL x. OPTION_JOIN (Some x) = x)"
  by simp

lemma PAIR: "(fst x,snd x) = x"
  by simp

lemma PAIR_MAP: "map_pair f g p = (f (fst p),g (snd p))"
  by (simp add: map_pair_def split_def)

lemma pair_case_def: "split = split"
  ..

lemma LESS_OR_EQ: "m <= (n::nat) = (m < n | m = n)"
  by auto

definition nat_gt :: "nat => nat => bool" where
  "nat_gt == %m n. n < m"

definition nat_ge :: "nat => nat => bool" where
  "nat_ge == %m n. nat_gt m n | m = n"

lemma [import_rew]: "nat_gt m n = (n < m)"
  by (simp add: nat_gt_def)

lemma [import_rew]: "nat_ge m n = (n <= m)"
  by (auto simp add: nat_ge_def nat_gt_def)

lemma GREATER_DEF: "ALL m n. (n < m) = (n < m)"
  by simp

lemma GREATER_OR_EQ: "ALL m n. n <= (m::nat) = (n < m | m = n)"
  by auto

lemma LESS_DEF: "m < n = (? P. (!n. P (Suc n) --> P n) & P m & ~P n)"
proof safe
  assume 1: "m < n"
  def P == "%n. n <= m"
  have "(!n. P (Suc n) \<longrightarrow> P n) & P m & ~P n"
  proof (auto simp add: P_def)
    assume "n <= m"
    with 1
    show False
      by auto
  qed
  thus "? P. (!n. P (Suc n) \<longrightarrow> P n) & P m & ~P n"
    by auto
next
  fix P
  assume alln: "!n. P (Suc n) \<longrightarrow> P n"
  assume pm: "P m"
  assume npn: "~P n"
  have "!k q. q + k = m \<longrightarrow> P q"
  proof
    fix k
    show "!q. q + k = m \<longrightarrow> P q"
    proof (induct k,simp_all)
      show "P m" by fact
    next
      fix k
      assume ind: "!q. q + k = m \<longrightarrow> P q"
      show "!q. Suc (q + k) = m \<longrightarrow> P q"
      proof (rule+)
        fix q
        assume "Suc (q + k) = m"
        hence "(Suc q) + k = m"
          by simp
        with ind
        have psq: "P (Suc q)"
          by simp
        from alln
        have "P (Suc q) --> P q"
          ..
        with psq
        show "P q"
          by simp
      qed
    qed
  qed
  hence "!q. q + (m - n) = m \<longrightarrow> P q"
    ..
  hence hehe: "n + (m - n) = m \<longrightarrow> P n"
    ..
  show "m < n"
  proof (rule classical)
    assume "~(m<n)"
    hence "n <= m"
      by simp
    with hehe
    have "P n"
      by simp
    with npn
    show "m < n"
      ..
  qed
qed

definition FUNPOW :: "('a => 'a) => nat => 'a => 'a" where
  "FUNPOW f n == f ^^ n"

lemma FUNPOW: "(ALL f x. (f ^^ 0) x = x) &
  (ALL f n x. (f ^^ Suc n) x = (f ^^ n) (f x))"
  by (simp add: funpow_swap1)

lemma [import_rew]: "FUNPOW f n = f ^^ n"
  by (simp add: FUNPOW_def)

lemma ADD: "(!n. (0::nat) + n = n) & (!m n. Suc m + n = Suc (m + n))"
  by simp

lemma MULT: "(!n. (0::nat) * n = 0) & (!m n. Suc m * n = m * n + n)"
  by simp

lemma SUB: "(!m. (0::nat) - m = 0) & (!m n. (Suc m) - n = (if m < n then 0 else Suc (m - n)))"
  by (simp) arith

lemma MAX_DEF: "max (m::nat) n = (if m < n then n else m)"
  by (simp add: max_def)

lemma MIN_DEF: "min (m::nat) n = (if m < n then m else n)"
  by (simp add: min_def)

lemma DIVISION: "(0::nat) < n --> (!k. (k = k div n * n + k mod n) & k mod n < n)"
  by simp

definition ALT_ZERO :: nat where 
  "ALT_ZERO == 0"

definition NUMERAL_BIT1 :: "nat \<Rightarrow> nat" where 
  "NUMERAL_BIT1 n == n + (n + Suc 0)"

definition NUMERAL_BIT2 :: "nat \<Rightarrow> nat" where 
  "NUMERAL_BIT2 n == n + (n + Suc (Suc 0))"

definition NUMERAL :: "nat \<Rightarrow> nat" where 
  "NUMERAL x == x"

lemma [import_rew]: "NUMERAL ALT_ZERO = 0"
  by (simp add: ALT_ZERO_def NUMERAL_def)

lemma [import_rew]: "NUMERAL (NUMERAL_BIT1 ALT_ZERO) = 1"
  by (simp add: ALT_ZERO_def NUMERAL_BIT1_def NUMERAL_def)

lemma [import_rew]: "NUMERAL (NUMERAL_BIT2 ALT_ZERO) = 2"
  by (simp add: ALT_ZERO_def NUMERAL_BIT2_def NUMERAL_def)

lemma EXP: "(!m. m ^ 0 = (1::nat)) & (!m n. m ^ Suc n = m * (m::nat) ^ n)"
  by auto

lemma num_case_def: "(!b f. nat_case b f 0 = b) & (!b f n. nat_case b f (Suc n) = f n)"
  by simp

lemma divides_def: "(a::nat) dvd b = (? q. b = q * a)"
  by (auto simp add: dvd_def)

lemma list_case_def: "(!v f. list_case v f [] = v) & (!v f a0 a1. list_case v f (a0#a1) = f a0 a1)"
  by simp

primrec list_size :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "list_size f [] = 0"
| "list_size f (a0#a1) = 1 + (f a0 + list_size f a1)"

lemma list_size_def': "(!f. list_size f [] = 0) &
         (!f a0 a1. list_size f (a0#a1) = 1 + (f a0 + list_size f a1))"
  by simp

lemma list_case_cong: "! M M' v f. M = M' & (M' = [] \<longrightarrow>  v = v') &
           (!a0 a1. (M' = a0#a1) \<longrightarrow> (f a0 a1 = f' a0 a1)) -->
           (list_case v f M = list_case v' f' M')"
proof clarify
  fix M M' v f
  assume 1: "M' = [] \<longrightarrow> v = v'"
    and 2: "!a0 a1. M' = a0 # a1 \<longrightarrow> f a0 a1 = f' a0 a1"
  show "list_case v f M' = list_case v' f' M'"
  proof (rule List.list.case_cong)
    show "M' = M'"
      ..
  next
    assume "M' = []"
    with 1 2
    show "v = v'"
      by auto
  next
    fix a0 a1
    assume "M' = a0 # a1"
    with 1 2
    show "f a0 a1 = f' a0 a1"
      by auto
  qed
qed

lemma list_Axiom: "ALL f0 f1. EX fn. (fn [] = f0) & (ALL a0 a1. fn (a0#a1) = f1 a0 a1 (fn a1))"
proof safe
  fix f0 f1
  def fn == "list_rec f0 f1"
  have "fn [] = f0 & (ALL a0 a1. fn (a0 # a1) = f1 a0 a1 (fn a1))"
    by (simp add: fn_def)
  thus "EX fn. fn [] = f0 & (ALL a0 a1. fn (a0 # a1) = f1 a0 a1 (fn a1))"
    by auto
qed

lemma list_Axiom_old: "EX! fn. (fn [] = x) & (ALL h t. fn (h#t) = f (fn t) h t)"
proof safe
  def fn == "list_rec x (%h t r. f r h t)"
  have "fn [] = x & (ALL h t. fn (h # t) = f (fn t) h t)"
    by (simp add: fn_def)
  thus "EX fn. fn [] = x & (ALL h t. fn (h # t) = f (fn t) h t)"
    by auto
next
  fix fn1 fn2
  assume 1: "ALL h t. fn1 (h # t) = f (fn1 t) h t"
  assume 2: "ALL h t. fn2 (h # t) = f (fn2 t) h t"
  assume 3: "fn2 [] = fn1 []"
  show "fn1 = fn2"
  proof
    fix xs
    show "fn1 xs = fn2 xs"
      by (induct xs) (simp_all add: 1 2 3) 
  qed
qed

lemma NULL_DEF: "(List.null [] = True) & (!h t. List.null (h # t) = False)"
  by (simp add: null_def)

definition sum :: "nat list \<Rightarrow> nat" where
  "sum l == foldr (op +) l 0"

lemma SUM: "(sum [] = 0) & (!h t. sum (h#t) = h + sum t)"
  by (simp add: sum_def)

lemma APPEND: "(!l. [] @ l = l) & (!l1 l2 h. (h#l1) @ l2 = h# l1 @ l2)"
  by simp

lemma FLAT: "(concat [] = []) & (!h t. concat (h#t) = h @ (concat t))"
  by simp

lemma LENGTH: "(length [] = 0) & (!h t. length (h#t) = Suc (length t))"
  by simp

lemma MAP: "(!f. map f [] = []) & (!f h t. map f (h#t) = f h#map f t)"
  by simp

lemma MEM: "(!x. List.member [] x = False) & (!x h t. List.member (h#t) x = ((x = h) | List.member t x))"
  by (simp add: member_def)

lemma FILTER: "(!P. filter P [] = []) & (!P h t.
           filter P (h#t) = (if P h then h#filter P t else filter P t))"
  by simp

lemma REPLICATE: "(ALL x. replicate 0 x = []) &
  (ALL n x. replicate (Suc n) x = x # replicate n x)"
  by simp

definition FOLDR :: "[['a,'b]\<Rightarrow>'b,'b,'a list] \<Rightarrow> 'b" where
  "FOLDR f e l == foldr f l e"

lemma [import_rew]: "FOLDR f e l = foldr f l e"
  by (simp add: FOLDR_def)

lemma FOLDR: "(!f e. foldr f [] e = e) & (!f e x l. foldr f (x#l) e = f x (foldr f l e))"
  by simp

lemma FOLDL: "(!f e. foldl f e [] = e) & (!f e x l. foldl f e (x#l) = foldl f (f e x) l)"
  by simp

lemma EVERY_DEF: "(!P. list_all P [] = True) & (!P h t. list_all P (h#t) = (P h & list_all P t))"
  by simp

lemma list_exists_DEF: "(!P. list_ex P [] = False) & (!P h t. list_ex P (h#t) = (P h | list_ex P t))"
  by simp

primrec map2 :: "[['a,'b]\<Rightarrow>'c,'a list,'b list] \<Rightarrow> 'c list" where
  map2_Nil: "map2 f [] l2 = []"
| map2_Cons: "map2 f (x#xs) l2 = f x (hd l2) # map2 f xs (tl l2)"

lemma MAP2: "(!f. map2 f [] [] = []) & (!f h1 t1 h2 t2. map2 f (h1#t1) (h2#t2) = f h1 h2#map2 f t1 t2)"
  by simp

lemma list_INDUCT: "\<lbrakk> P [] ; !t. P t \<longrightarrow> (!h. P (h#t)) \<rbrakk> \<Longrightarrow> !l. P l"
proof
  fix l
  assume "P []"
  assume allt: "!t. P t \<longrightarrow> (!h. P (h # t))"
  show "P l"
  proof (induct l)
    show "P []" by fact
  next
    fix h t
    assume "P t"
    with allt
    have "!h. P (h # t)"
      by auto
    thus "P (h # t)"
      ..
  qed
qed

lemma list_CASES: "(l = []) | (? t h. l = h#t)"
  by (induct l,auto)

definition ZIP :: "'a list * 'b list \<Rightarrow> ('a * 'b) list" where
  "ZIP == %(a,b). zip a b"

lemma ZIP: "(zip [] [] = []) &
  (!x1 l1 x2 l2. zip (x1#l1) (x2#l2) = (x1,x2)#zip l1 l2)"
  by simp

lemma [import_rew]: "ZIP (a,b) = zip a b"
  by (simp add: ZIP_def)

primrec unzip :: "('a * 'b) list \<Rightarrow> 'a list * 'b list" where
  unzip_Nil: "unzip [] = ([],[])"
| unzip_Cons: "unzip (xy#xys) = (let zs = unzip xys in (fst xy # fst zs,snd xy # snd zs))"

lemma UNZIP: "(unzip [] = ([],[])) &
         (!x l. unzip (x#l) = (fst x#fst (unzip l),snd x#snd (unzip l)))"
  by (simp add: Let_def)

lemma REVERSE: "(rev [] = []) & (!h t. rev (h#t) = (rev t) @ [h])"
  by simp

lemma REAL_SUP_ALLPOS: "\<lbrakk> ALL x. P (x::real) \<longrightarrow> 0 < x ; EX x. P x; EX z. ALL x. P x \<longrightarrow> x < z \<rbrakk> \<Longrightarrow> EX s. ALL y. (EX x. P x & y < x) = (y < s)"
proof safe
  fix x z
  assume allx: "ALL x. P x \<longrightarrow> 0 < x"
  assume px: "P x"
  assume allx': "ALL x. P x \<longrightarrow> x < z"
  have "EX s. ALL y. (EX x : Collect P. y < x) = (y < s)"
  proof (rule posreal_complete)
    from px
    show "EX x. x : Collect P"
      by auto
  next
    from allx'
    show "EX y. ALL x : Collect P. x < y"
      apply simp
      ..
  qed
  thus "EX s. ALL y. (EX x. P x & y < x) = (y < s)"
    by simp
qed

lemma REAL_10: "~((1::real) = 0)"
  by simp

lemma REAL_ADD_ASSOC: "(x::real) + (y + z) = x + y + z"
  by simp

lemma REAL_MUL_ASSOC: "(x::real) * (y * z) = x * y * z"
  by simp

lemma REAL_ADD_LINV:  "-x + x = (0::real)"
  by simp

lemma REAL_MUL_LINV: "x ~= (0::real) ==> inverse x * x = 1"
  by simp

lemma REAL_LT_TOTAL: "((x::real) = y) | x < y | y < x"
  by auto

lemma [import_rew]: "real (0::nat) = 0"
  by simp

lemma [import_rew]: "real (1::nat) = 1"
  by simp

lemma [import_rew]: "real (2::nat) = 2"
  by simp

lemma real_lte: "((x::real) <= y) = (~(y < x))"
  by auto

lemma real_of_num: "((0::real) = 0) & (!n. real (Suc n) = real n + 1)"
  by (simp add: real_of_nat_Suc)

lemma abs: "abs (x::real) = (if 0 <= x then x else -x)"
  by (simp add: abs_if)

lemma pow: "(!x::real. x ^ 0 = 1) & (!x::real. ALL n. x ^ (Suc n) = x * x ^ n)"
  by simp

definition real_gt :: "real => real => bool" where 
  "real_gt == %x y. y < x"

lemma [import_rew]: "real_gt x y = (y < x)"
  by (simp add: real_gt_def)

lemma real_gt: "ALL x (y::real). (y < x) = (y < x)"
  by simp

definition real_ge :: "real => real => bool" where
  "real_ge x y == y <= x"

lemma [import_rew]: "real_ge x y = (y <= x)"
  by (simp add: real_ge_def)

lemma real_ge: "ALL x y. (y <= x) = (y <= x)"
  by simp

definition [import_rew]: "list_mem x xs = List.member xs x"

end
