(*  Title:      HOL/ex/Tree23.thy
    Author:     Tobias Nipkow, TU Muenchen
*)

header {* 2-3 Trees *}

theory Tree23
imports Main
begin

text{* This is a very direct translation of some of the functions in table.ML
in the Isabelle source code. That source is due to Makarius Wenzel and Stefan
Berghofer.

So far this file contains only data types and functions, but no proofs. Feel
free to have a go at the latter!

Note that because of complicated patterns and mutual recursion, these
function definitions take a few minutes and can also be seen as stress tests
for the function definition facility.  *}

type_synonym key = int -- {*for simplicity, should be a type class*}

datatype ord = LESS | EQUAL | GREATER

definition "ord i j = (if i<j then LESS else if i=j then EQUAL else GREATER)"

datatype 'a tree23 =
  Empty |
  Branch2 "'a tree23" "key * 'a" "'a tree23" |
  Branch3 "'a tree23" "key * 'a" "'a tree23" "key * 'a" "'a tree23"

datatype 'a growth =
  Stay "'a tree23" |
  Sprout "'a tree23" "key * 'a" "'a tree23"

fun add :: "key \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a growth" where
"add key y Empty = Sprout Empty (key,y) Empty" |
"add key y (Branch2 left (k,x) right) =
   (case ord key k of
      LESS =>
        (case add key y left of
           Stay left' => Stay (Branch2 left' (k,x) right)
         | Sprout left1 q left2
           => Stay (Branch3 left1 q left2 (k,x) right))
    | EQUAL => Stay (Branch2 left (k,y) right)
    | GREATER =>
        (case add key y right of
           Stay right' => Stay (Branch2 left (k,x) right')
         | Sprout right1 q right2
           => Stay (Branch3 left (k,x) right1 q right2)))" |
"add key y (Branch3 left (k1,x1) mid (k2,x2) right) =
   (case ord key k1 of
      LESS =>
        (case add key y left of
           Stay left' => Stay (Branch3 left' (k1,x1) mid (k2,x2) right)
         | Sprout left1 q left2
           => Sprout (Branch2 left1 q left2) (k1,x1) (Branch2 mid (k2,x2) right))
    | EQUAL => Stay (Branch3 left (k1,y) mid (k2,x2) right)
    | GREATER =>
        (case ord key k2 of
           LESS =>
             (case add key y mid of
                Stay mid' => Stay (Branch3 left (k1,x1) mid' (k2,x2) right)
              | Sprout mid1 q mid2
                => Sprout (Branch2 left (k1,x1) mid1) q (Branch2 mid2 (k2,x2) right))
         | EQUAL => Stay (Branch3 left (k1,x1) mid (k2,y) right)
         | GREATER =>
             (case add key y right of
                Stay right' => Stay (Branch3 left (k1,x1) mid (k2,x2) right')
              | Sprout right1 q right2
                => Sprout (Branch2 left (k1,x1) mid) (k2,x2) (Branch2 right1 q right2))))"

definition add0 :: "key \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
"add0 k y t =
  (case add k y t of Stay t' => t' | Sprout l p r => Branch2 l p r)"

value "add0 5 e (add0 4 d (add0 3 c (add0 2 b (add0 1 a Empty))))"

fun compare where
"compare None (k2, _) = LESS" |
"compare (Some k1) (k2, _) = ord k1 k2"

fun if_eq where
"if_eq EQUAL x y = x" |
"if_eq _ x y = y"

fun del :: "key option \<Rightarrow> 'a tree23 \<Rightarrow> ((key * 'a) * bool * 'a tree23)option"
where
"del (Some k) Empty = None" |
"del None (Branch2 Empty p Empty) = Some(p, (True, Empty))" |
"del None (Branch3 Empty p Empty q Empty) = Some(p, (False, Branch2 Empty q Empty))" |
"del k (Branch2 Empty p Empty) = (case compare k p of
      EQUAL => Some(p, (True, Empty)) | _ => None)" |
"del k (Branch3 Empty p Empty q Empty) = (case compare k p of
      EQUAL => Some(p, (False, Branch2 Empty q Empty))
    | _ => (case compare k q of
        EQUAL => Some(q, (False, Branch2 Empty p Empty))
      | _ => None))" |
"del k (Branch2 l p r) = (case compare k p of
      LESS => (case del k l of None \<Rightarrow> None |
        Some(p', (False, l')) => Some(p', (False, Branch2 l' p r))
      | Some(p', (True, l')) => Some(p', case r of
          Branch2 rl rp rr => (True, Branch3 l' p rl rp rr)
        | Branch3 rl rp rm rq rr => (False, Branch2
            (Branch2 l' p rl) rp (Branch2 rm rq rr))))
    | or => (case del (if_eq or None k) r of None \<Rightarrow> None |
        Some(p', (False, r')) => Some(p', (False, Branch2 l (if_eq or p' p) r'))
      | Some(p', (True, r')) => Some(p', case l of
          Branch2 ll lp lr => (True, Branch3 ll lp lr (if_eq or p' p) r')
        | Branch3 ll lp lm lq lr => (False, Branch2
            (Branch2 ll lp lm) lq (Branch2 lr (if_eq or p' p) r')))))" |
"del k (Branch3 l p m q r) = (case compare k q of
      LESS => (case compare k p of
        LESS => (case del k l of None \<Rightarrow> None |
          Some(p', (False, l')) => Some(p', (False, Branch3 l' p m q r))
        | Some(p', (True, l')) => Some(p', (False, case (m, r) of
            (Branch2 ml mp mr, Branch2 _ _ _) => Branch2 (Branch3 l' p ml mp mr) q r
          | (Branch3 ml mp mm mq mr, _) => Branch3 (Branch2 l' p ml) mp (Branch2 mm mq mr) q r
          | (Branch2 ml mp mr, Branch3 rl rp rm rq rr) =>
              Branch3 (Branch2 l' p ml) mp (Branch2 mr q rl) rp (Branch2 rm rq rr))))
      | or => (case del (if_eq or None k) m of None \<Rightarrow> None |
          Some(p', (False, m')) => Some(p', (False, Branch3 l (if_eq or p' p) m' q r))
        | Some(p', (True, m')) => Some(p', (False, case (l, r) of
            (Branch2 ll lp lr, Branch2 _ _ _) => Branch2 (Branch3 ll lp lr (if_eq or p' p) m') q r
          | (Branch3 ll lp lm lq lr, _) => Branch3 (Branch2 ll lp lm) lq (Branch2 lr (if_eq or p' p) m') q r
          | (_, Branch3 rl rp rm rq rr) => Branch3 l (if_eq or p' p) (Branch2 m' q rl) rp (Branch2 rm rq rr)))))
    | or => (case del (if_eq or None k) r of None \<Rightarrow> None |
        Some(q', (False, r')) => Some(q', (False, Branch3 l p m (if_eq or q' q) r'))
      | Some(q', (True, r')) => Some(q', (False, case (l, m) of
          (Branch2 _ _ _, Branch2 ml mp mr) => Branch2 l p (Branch3 ml mp mr (if_eq or q' q) r')
        | (_, Branch3 ml mp mm mq mr) => Branch3 l p (Branch2 ml mp mm) mq (Branch2 mr (if_eq or q' q) r')
        | (Branch3 ll lp lm lq lr, Branch2 ml mp mr) =>
            Branch3 (Branch2 ll lp lm) lq (Branch2 lr p ml) mp (Branch2 mr (if_eq or q' q) r')))))"

definition del0 :: "key \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
"del0 k t = (case del (Some k) t of None \<Rightarrow> t | Some(_,(_,t')) \<Rightarrow> t')"


(* yes, this is rather slow *)
fun ord0 :: "'a tree23 \<Rightarrow> bool"
and ordl :: "key \<Rightarrow> 'a tree23 \<Rightarrow> bool"
and ordr :: "'a tree23 \<Rightarrow> key \<Rightarrow> bool"
and ordlr :: "key \<Rightarrow> 'a tree23 \<Rightarrow> key \<Rightarrow> bool"
where
"ord0 Empty = True" |
"ord0 (Branch2 l p r)  = (ordr l (fst p) & ordl (fst p) r)" |
"ord0 (Branch3 l p m q r)  = (ordr l (fst p) & ordlr (fst p) m (fst q) & ordl (fst q) r)" |

"ordl _ Empty = True" |
"ordl x (Branch2 l p r)  = (ordlr x l (fst p) & ordl (fst p) r)" |
"ordl x (Branch3 l p m q r)  = (ordlr x l (fst p) & ordlr (fst p) m (fst q) & ordl (fst q) r)" |

"ordr Empty _ = True" |
"ordr (Branch2 l p r) x = (ordr l (fst p) & ordlr (fst p) r x)" |
"ordr (Branch3 l p m q r) x = (ordr l (fst p) & ordlr (fst p) m (fst q) & ordlr (fst q) r x)" |

"ordlr x Empty y = (x < y)" |
"ordlr x (Branch2 l p r) y = (ordlr x l (fst p) & ordlr (fst p) r y)" |
"ordlr x (Branch3 l p m q r) y = (ordlr x l (fst p) & ordlr (fst p) m (fst q) & ordlr (fst q) r y)"

definition opt_less :: "key option \<Rightarrow> key option \<Rightarrow> bool" where
  "opt_less x y = (case x of None \<Rightarrow> True | Some a \<Rightarrow> (case y of None \<Rightarrow> True | Some b \<Rightarrow> a < b))"

lemma opt_less_simps [simp]:
  "opt_less None y = True"
  "opt_less x None = True"
  "opt_less (Some a) (Some b) = (a < b)"
unfolding opt_less_def by (auto simp add: ord_def split: option.split)

fun ord' :: "key option \<Rightarrow> 'a tree23 \<Rightarrow> key option \<Rightarrow> bool" where
"ord' x Empty y = opt_less x y" |
"ord' x (Branch2 l p r) y = (ord' x l (Some (fst p)) & ord' (Some (fst p)) r y)" |
"ord' x (Branch3 l p m q r) y = (ord' x l (Some (fst p)) & ord' (Some (fst p)) m (Some (fst q)) & ord' (Some (fst q)) r y)"

lemma ord':
  "ord' x t y = (case x of None \<Rightarrow> (case y of None \<Rightarrow> ord0 t | Some y' \<Rightarrow> ordr t y')
    | Some x' \<Rightarrow> (case y of None \<Rightarrow> ordl x' t | Some y' \<Rightarrow> ordlr x' t y'))"
by (induct t arbitrary: x y, auto simp add: opt_less_def split: option.split)

fun height :: "'a tree23 \<Rightarrow> nat" where
"height Empty = 0" |
"height (Branch2 l _ r) = Suc(max (height l) (height r))" |
"height (Branch3 l _ m _ r) = Suc(max (height l) (max (height m) (height r)))"

text{* Is a tree balanced? *}
fun bal :: "'a tree23 \<Rightarrow> bool" where
"bal Empty = True" |
"bal (Branch2 l _ r) = (bal l & bal r & height l = height r)" |
"bal (Branch3 l _ m _ r) = (bal l & bal m & bal r & height l = height m & height m = height r)"

text {* The @{term "add0"} function either preserves the height of the
tree, or increases it by one. The constructor returned by the @{term
"add"} function determines which: A return value of the form @{term
"Stay t"} indicates that the height will be the same. A value of the
form @{term "Sprout l p r"} indicates an increase in height. *}

fun gheight :: "'a growth \<Rightarrow> nat" where
"gheight (Stay t) = height t" |
"gheight (Sprout l p r) = max (height l) (height r)"

lemma gheight_add: "gheight (add k y t) = height t"
 apply (induct t)
   apply simp
  apply clarsimp
  apply (case_tac "ord k a")
    apply simp
    apply (case_tac "add k y t1", simp, simp)
   apply simp
  apply simp
  apply (case_tac "add k y t2", simp, simp)
 apply clarsimp
 apply (case_tac "ord k a")
   apply simp
   apply (case_tac "add k y t1", simp, simp)
  apply simp
 apply simp
 apply (case_tac "ord k aa")
   apply simp
   apply (case_tac "add k y t2", simp, simp)
  apply simp
 apply simp
 apply (case_tac "add k y t3", simp, simp)
done

lemma add_eq_Stay_dest: "add k y t = Stay t' \<Longrightarrow> height t = height t'"
  using gheight_add [of k y t] by simp

lemma add_eq_Sprout_dest: "add k y t = Sprout l p r \<Longrightarrow> height t = max (height l) (height r)"
  using gheight_add [of k y t] by simp

definition gtree :: "'a growth \<Rightarrow> 'a tree23" where
  "gtree g = (case g of Stay t \<Rightarrow> t | Sprout l p r \<Rightarrow> Branch2 l p r)"

lemma gtree_simps [simp]:
  "gtree (Stay t) = t"
  "gtree (Sprout l p r) = Branch2 l p r"
unfolding gtree_def by simp_all

lemma add0: "add0 k y t = gtree (add k y t)"
  unfolding add0_def by (simp split: growth.split)

text {* The @{term "add0"} operation preserves balance. *}

lemma bal_add0: "bal t \<Longrightarrow> bal (add0 k y t)"
unfolding add0
 apply (induct t)
   apply simp
  apply clarsimp
  apply (case_tac "ord k a")
    apply simp
    apply (case_tac "add k y t1")
     apply (simp, drule add_eq_Stay_dest, simp)
    apply (simp, drule add_eq_Sprout_dest, simp)
   apply simp
  apply simp
  apply (case_tac "add k y t2")
   apply (simp, drule add_eq_Stay_dest, simp)
  apply (simp, drule add_eq_Sprout_dest, simp)
 apply clarsimp
 apply (case_tac "ord k a")
   apply simp
   apply (case_tac "add k y t1")
    apply (simp, drule add_eq_Stay_dest, simp)
   apply (simp, drule add_eq_Sprout_dest, simp)
  apply simp
 apply simp
 apply (case_tac "ord k aa")
   apply simp
   apply (case_tac "add k y t2")
    apply (simp, drule add_eq_Stay_dest, simp)
   apply (simp, drule add_eq_Sprout_dest, simp)
  apply simp
 apply simp
 apply (case_tac "add k y t3")
  apply (simp, drule add_eq_Stay_dest, simp)
 apply (simp, drule add_eq_Sprout_dest, simp)
done

text {* The @{term "add0"} operation preserves order. *}

lemma ord_cases:
  fixes a b :: int obtains
  "ord a b = LESS" and "a < b" |
  "ord a b = EQUAL" and "a = b" |
  "ord a b = GREATER" and "a > b"
unfolding ord_def by (rule linorder_cases [of a b]) auto

lemma ord'_add0:
  "\<lbrakk>ord' k1 t k2; opt_less k1 (Some k); opt_less (Some k) k2\<rbrakk> \<Longrightarrow> ord' k1 (add0 k y t) k2"
unfolding add0
 apply (induct t arbitrary: k1 k2)
   apply simp
  apply clarsimp
  apply (rule_tac a=k and b=a in ord_cases)
    apply simp
    apply (case_tac "add k y t1", simp, simp)
   apply simp
  apply simp
  apply (case_tac "add k y t2", simp, simp)
 apply clarsimp
 apply (rule_tac a=k and b=a in ord_cases)
   apply simp
   apply (case_tac "add k y t1", simp, simp)
  apply simp
 apply simp
 apply (rule_tac a=k and b=aa in ord_cases)
   apply simp
   apply (case_tac "add k y t2", simp, simp)
  apply simp
 apply simp
 apply (case_tac "add k y t3", simp, simp)
done

lemma ord0_add0: "ord0 t \<Longrightarrow> ord0 (add0 k y t)"
using ord'_add0 [of None t None k y] by (simp add: ord')

text {* The @{term "del"} function preserves balance. *}

lemma del_extra_simps:
"l \<noteq> Empty \<or> r \<noteq> Empty \<Longrightarrow>
 del k (Branch2 l p r) = (case compare k p of
      LESS => (case del k l of None \<Rightarrow> None |
        Some(p', (False, l')) => Some(p', (False, Branch2 l' p r))
      | Some(p', (True, l')) => Some(p', case r of
          Branch2 rl rp rr => (True, Branch3 l' p rl rp rr)
        | Branch3 rl rp rm rq rr => (False, Branch2
            (Branch2 l' p rl) rp (Branch2 rm rq rr))))
    | or => (case del (if_eq or None k) r of None \<Rightarrow> None |
        Some(p', (False, r')) => Some(p', (False, Branch2 l (if_eq or p' p) r'))
      | Some(p', (True, r')) => Some(p', case l of
          Branch2 ll lp lr => (True, Branch3 ll lp lr (if_eq or p' p) r')
        | Branch3 ll lp lm lq lr => (False, Branch2
            (Branch2 ll lp lm) lq (Branch2 lr (if_eq or p' p) r')))))"
"l \<noteq> Empty \<or> m \<noteq> Empty \<or> r \<noteq> Empty \<Longrightarrow>
 del k (Branch3 l p m q r) = (case compare k q of
      LESS => (case compare k p of
        LESS => (case del k l of None \<Rightarrow> None |
          Some(p', (False, l')) => Some(p', (False, Branch3 l' p m q r))
        | Some(p', (True, l')) => Some(p', (False, case (m, r) of
            (Branch2 ml mp mr, Branch2 _ _ _) => Branch2 (Branch3 l' p ml mp mr) q r
          | (Branch3 ml mp mm mq mr, _) => Branch3 (Branch2 l' p ml) mp (Branch2 mm mq mr) q r
          | (Branch2 ml mp mr, Branch3 rl rp rm rq rr) =>
              Branch3 (Branch2 l' p ml) mp (Branch2 mr q rl) rp (Branch2 rm rq rr))))
      | or => (case del (if_eq or None k) m of None \<Rightarrow> None |
          Some(p', (False, m')) => Some(p', (False, Branch3 l (if_eq or p' p) m' q r))
        | Some(p', (True, m')) => Some(p', (False, case (l, r) of
            (Branch2 ll lp lr, Branch2 _ _ _) => Branch2 (Branch3 ll lp lr (if_eq or p' p) m') q r
          | (Branch3 ll lp lm lq lr, _) => Branch3 (Branch2 ll lp lm) lq (Branch2 lr (if_eq or p' p) m') q r
          | (_, Branch3 rl rp rm rq rr) => Branch3 l (if_eq or p' p) (Branch2 m' q rl) rp (Branch2 rm rq rr)))))
    | or => (case del (if_eq or None k) r of None \<Rightarrow> None |
        Some(q', (False, r')) => Some(q', (False, Branch3 l p m (if_eq or q' q) r'))
      | Some(q', (True, r')) => Some(q', (False, case (l, m) of
          (Branch2 _ _ _, Branch2 ml mp mr) => Branch2 l p (Branch3 ml mp mr (if_eq or q' q) r')
        | (_, Branch3 ml mp mm mq mr) => Branch3 l p (Branch2 ml mp mm) mq (Branch2 mr (if_eq or q' q) r')
        | (Branch3 ll lp lm lq lr, Branch2 ml mp mr) =>
            Branch3 (Branch2 ll lp lm) lq (Branch2 lr p ml) mp (Branch2 mr (if_eq or q' q) r')))))"
apply -
apply (cases l, cases r, simp_all only: del.simps, simp)
apply (cases l, cases m, cases r, simp_all only: del.simps, simp)
done

inductive full :: "nat \<Rightarrow> 'a tree23 \<Rightarrow> bool" where
"full 0 Empty" |
"\<lbrakk>full n l; full n r\<rbrakk> \<Longrightarrow> full (Suc n) (Branch2 l p r)" |
"\<lbrakk>full n l; full n m; full n r\<rbrakk> \<Longrightarrow> full (Suc n) (Branch3 l p m q r)"

inductive_cases full_elims:
  "full n Empty"
  "full n (Branch2 l p r)"
  "full n (Branch3 l p m q r)"

inductive_cases full_0_elim: "full 0 t"
inductive_cases full_Suc_elim: "full (Suc n) t"

lemma full_0_iff [simp]: "full 0 t \<longleftrightarrow> t = Empty"
  by (auto elim: full_0_elim intro: full.intros)

lemma full_Empty_iff [simp]: "full n Empty \<longleftrightarrow> n = 0"
  by (auto elim: full_elims intro: full.intros)

lemma full_Suc_Branch2_iff [simp]:
  "full (Suc n) (Branch2 l p r) \<longleftrightarrow> full n l \<and> full n r"
  by (auto elim: full_elims intro: full.intros)

lemma full_Suc_Branch3_iff [simp]:
  "full (Suc n) (Branch3 l p m q r) \<longleftrightarrow> full n l \<and> full n m \<and> full n r"
  by (auto elim: full_elims intro: full.intros)

definition
  "full_del n k t = (case del k t of None \<Rightarrow> True | Some (p, b, t') \<Rightarrow> full (if b then n else Suc n) t')"

lemmas ord_case = ord.exhaust [where y=y and P="ord_case a b c y", standard]
lemmas option_ord_case = ord.exhaust [where y=y and P="option_case a b (ord_case d e f y)", standard]
lemmas option_option_case = option.exhaust [where y=y and P="option_case a b (option_case d e y)", standard]
lemmas option_prod_case = prod.exhaust [where y=y and P="option_case a b (prod_case c y)", standard]
lemmas option_bool_case = bool.exhaust [where y=y and P="option_case a b (bool_case c d y)", standard]
lemmas prod_tree23_case = tree23.exhaust [where y=y and P="prod_case a (tree23_case b c d y)", standard]
lemmas option_case = option.exhaust [where y=y and P="option_case a b y", standard]
lemmas full_tree23_case = tree23.exhaust [where y=y and P="full a (tree23_case b c d y)", standard]

lemmas case_intros =
  option_ord_case option_option_case option_prod_case option_bool_case prod_tree23_case option_case
  full_tree23_case

lemma full_del: "full (Suc n) t \<Longrightarrow> full_del n k t"
proof -
  { fix n :: "nat" and p :: "key \<times> 'a" and l r :: "'a tree23" and k
    assume "\<And>n. \<lbrakk>compare k p = LESS; full (Suc n) l\<rbrakk> \<Longrightarrow> full_del n k l"
    and "\<And>n. \<lbrakk>compare k p = EQUAL; full (Suc n) r\<rbrakk> \<Longrightarrow> full_del n (if_eq EQUAL None k) r"
    and "\<And>n. \<lbrakk>compare k p = GREATER; full (Suc n) r\<rbrakk> \<Longrightarrow> full_del n (if_eq GREATER None k) r"
    and "full (Suc n) (Branch2 l p r)"
    hence "full_del n k (Branch2 l p r)"
     apply clarsimp
     apply (cases n)
      apply (cases k)
       apply (simp add: full_del_def)
      apply (simp add: full_del_def split: ord.split)
     apply (simp add: full_del_def)
     apply (subst del_extra_simps, force)
     apply (simp | rule case_intros)+
     done
  } note A = this
  { fix n :: "nat" and p q :: "key \<times> 'a" and l m r :: "'a tree23" and k
    assume "\<And>n. \<lbrakk>compare k q = LESS; compare k p = LESS; full (Suc n) l\<rbrakk> \<Longrightarrow> full_del n k l"
    and "\<And>n. \<lbrakk>compare k q = LESS; compare k p = EQUAL; full (Suc n) m\<rbrakk> \<Longrightarrow> full_del n (if_eq EQUAL None k) m"
    and "\<And>n. \<lbrakk>compare k q = LESS; compare k p = GREATER; full (Suc n) m\<rbrakk> \<Longrightarrow> full_del n (if_eq GREATER None k) m"
    and "\<And>n. \<lbrakk>compare k q = EQUAL; full (Suc n) r\<rbrakk> \<Longrightarrow> full_del n (if_eq EQUAL None k) r"
    and "\<And>n. \<lbrakk>compare k q = GREATER; full (Suc n) r\<rbrakk> \<Longrightarrow> full_del n (if_eq GREATER None k) r"
    and "full (Suc n) (Branch3 l p m q r)"
    hence "full_del n k (Branch3 l p m q r)"
     apply clarsimp
     apply (cases n)
      apply (cases k)
       apply (simp add: full_del_def)
      apply (simp add: full_del_def split: ord.split)
     apply (simp add: full_del_def)
     apply (subst del_extra_simps, force)
     apply (simp | rule case_intros)+
     done
  } note B = this
  show "full (Suc n) t \<Longrightarrow> full_del n k t"
  proof (induct k t arbitrary: n rule: del.induct)
    { case goal1 thus "full_del n (Some k) Empty"
        by simp }
    { case goal2 thus "full_del n None (Branch2 Empty p Empty)"
        unfolding full_del_def by auto }
    { case goal3 thus "full_del n None (Branch3 Empty p Empty q Empty)"
        unfolding full_del_def by auto }
    { case goal4 thus "full_del n (Some v) (Branch2 Empty p Empty)"
        unfolding full_del_def by (auto split: ord.split) }
    { case goal5 thus "full_del n (Some v) (Branch3 Empty p Empty q Empty)"
        unfolding full_del_def by (auto split: ord.split) }
    { case goal26 thus ?case by simp }
  qed (fact A | fact B)+
qed

lemma full_imp_height: "full n t \<Longrightarrow> height t = n"
  by (induct set: full, simp_all)

lemma full_imp_bal: "full n t \<Longrightarrow> bal t"
  by (induct set: full, auto dest: full_imp_height)

lemma bal_imp_full: "bal t \<Longrightarrow> full (height t) t"
  by (induct t, simp_all)

lemma bal_iff_full: "bal t \<longleftrightarrow> full (height t) t"
  using bal_imp_full full_imp_bal ..

lemma bal_del0: "bal t \<Longrightarrow> bal (del0 k t)"
  unfolding del0_def
  apply (drule bal_imp_full)
  apply (case_tac "height t", simp, simp)
  apply (frule full_del [where k="Some k"])
  apply (simp add: full_del_def)
  apply (auto split: option.split elim: full_imp_bal)
  done

text{* This is a little test harness and should be commented out once the
above functions have been proved correct. *}

datatype 'a act = Add int 'a | Del int

fun exec where
"exec [] t = t" |
"exec (Add k x # as) t = exec as (add0 k x t)" |
"exec (Del k # as) t = exec as (del0 k t)"

text{* Some quick checks: *}

lemma bal_exec: "bal t \<Longrightarrow> bal (exec as t)"
  by (induct as t arbitrary: t rule: exec.induct,
    simp_all add: bal_add0 bal_del0)

lemma "bal(exec as Empty)"
  by (simp add: bal_exec)

lemma "ord0(exec as Empty)"
quickcheck
oops

end
