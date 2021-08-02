(*  Title:      HOL/ex/Tree23.thy
    Author:     Tobias Nipkow, TU Muenchen
*)

section \<open>2-3 Trees\<close>

theory Tree23
imports Main
begin

hide_const (open) or

text\<open>This is a very direct translation of some of the functions in table.ML
in the Isabelle source code. That source is due to Makarius Wenzel and Stefan
Berghofer.

Note that because of complicated patterns and mutual recursion, these
function definitions take a few minutes and can also be seen as stress tests
for the function definition facility.\<close>

type_synonym key = int \<comment> \<open>for simplicity, should be a type class\<close>

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

text \<open>Ordered trees\<close>

definition opt_less :: "key option \<Rightarrow> key option \<Rightarrow> bool" where
  "opt_less x y = (case x of None \<Rightarrow> True | Some a \<Rightarrow> (case y of None \<Rightarrow> True | Some b \<Rightarrow> a < b))"

lemma opt_less_simps [simp]:
  "opt_less None y = True"
  "opt_less x None = True"
  "opt_less (Some a) (Some b) = (a < b)"
unfolding opt_less_def by (auto simp add: ord_def split: option.split)

primrec ord' :: "key option \<Rightarrow> 'a tree23 \<Rightarrow> key option \<Rightarrow> bool" where
"ord' x Empty y = opt_less x y" |
"ord' x (Branch2 l p r) y = (ord' x l (Some (fst p)) & ord' (Some (fst p)) r y)" |
"ord' x (Branch3 l p m q r) y = (ord' x l (Some (fst p)) & ord' (Some (fst p)) m (Some (fst q)) & ord' (Some (fst q)) r y)"

definition ord0 :: "'a tree23 \<Rightarrow> bool" where
  "ord0 t = ord' None t None"

text \<open>Balanced trees\<close>

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

fun height :: "'a tree23 \<Rightarrow> nat" where
"height Empty = 0" |
"height (Branch2 l _ r) = Suc(max (height l) (height r))" |
"height (Branch3 l _ m _ r) = Suc(max (height l) (max (height m) (height r)))"

text\<open>Is a tree balanced?\<close>
fun bal :: "'a tree23 \<Rightarrow> bool" where
"bal Empty = True" |
"bal (Branch2 l _ r) = (bal l & bal r & height l = height r)" |
"bal (Branch3 l _ m _ r) = (bal l & bal m & bal r & height l = height m & height m = height r)"

lemma full_imp_height: "full n t \<Longrightarrow> height t = n"
  by (induct set: full, simp_all)

lemma full_imp_bal: "full n t \<Longrightarrow> bal t"
  by (induct set: full, auto dest: full_imp_height)

lemma bal_imp_full: "bal t \<Longrightarrow> full (height t) t"
  by (induct t, simp_all)

lemma bal_iff_full: "bal t \<longleftrightarrow> (\<exists>n. full n t)"
  by (auto elim!: bal_imp_full full_imp_bal)

text \<open>The \<^term>\<open>add0\<close> function either preserves the height of the
tree, or increases it by one. The constructor returned by the \<^term>\<open>add\<close> function determines which: A return value of the form \<^term>\<open>Stay t\<close> indicates that the height will be the same. A value of the
form \<^term>\<open>Sprout l p r\<close> indicates an increase in height.\<close>

primrec gfull :: "nat \<Rightarrow> 'a growth \<Rightarrow> bool" where
"gfull n (Stay t) \<longleftrightarrow> full n t" |
"gfull n (Sprout l p r) \<longleftrightarrow> full n l \<and> full n r"

lemma gfull_add: "full n t \<Longrightarrow> gfull n (add k y t)"
by (induct set: full, auto split: ord.split growth.split)

text \<open>The \<^term>\<open>add0\<close> operation preserves balance.\<close>

lemma bal_add0: "bal t \<Longrightarrow> bal (add0 k y t)"
unfolding bal_iff_full add0_def
apply (erule exE)
apply (drule gfull_add [of _ _ k y])
apply (cases "add k y t")
apply (auto intro: full.intros)
done

text \<open>The \<^term>\<open>add0\<close> operation preserves order.\<close>

lemma ord_cases:
  fixes a b :: int obtains
  "ord a b = LESS" and "a < b" |
  "ord a b = EQUAL" and "a = b" |
  "ord a b = GREATER" and "a > b"
unfolding ord_def by (rule linorder_cases [of a b]) auto

definition gtree :: "'a growth \<Rightarrow> 'a tree23" where
  "gtree g = (case g of Stay t \<Rightarrow> t | Sprout l p r \<Rightarrow> Branch2 l p r)"

lemma gtree_simps [simp]:
  "gtree (Stay t) = t"
  "gtree (Sprout l p r) = Branch2 l p r"
unfolding gtree_def by simp_all

lemma add0: "add0 k y t = gtree (add k y t)"
  unfolding add0_def by (simp split: growth.split)

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
  by (simp add: ord0_def ord'_add0)

text \<open>The \<^term>\<open>del\<close> function preserves balance.\<close>

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

fun dfull where
"dfull n None \<longleftrightarrow> True" |
"dfull n (Some (p, (True, t'))) \<longleftrightarrow> full n t'" |
"dfull n (Some (p, (False, t'))) \<longleftrightarrow> full (Suc n) t'"

lemmas dfull_case_intros =
  ord.exhaust [of y "dfull a (case_ord b c d y)"]
  option.exhaust [of y "dfull a (case_option b c y)"]
  prod.exhaust [of y "dfull a (case_prod b y)"]
  bool.exhaust [of y "dfull a (case_bool b c y)"]
  tree23.exhaust [of y "dfull a (Some (b, case_tree23 c d e y))"]
  tree23.exhaust [of y "full a (case_tree23 b c d y)"]
  for a b c d e y

lemma dfull_del: "full (Suc n) t \<Longrightarrow> dfull n (del k t)"
proof -
  { fix n :: "nat" and p :: "key \<times> 'a" and l r :: "'a tree23" and k
    assume "\<And>n. \<lbrakk>compare k p = LESS; full (Suc n) l\<rbrakk> \<Longrightarrow> dfull n (del k l)"
    and "\<And>n. \<lbrakk>compare k p = EQUAL; full (Suc n) r\<rbrakk> \<Longrightarrow> dfull n (del (if_eq EQUAL None k) r)"
    and "\<And>n. \<lbrakk>compare k p = GREATER; full (Suc n) r\<rbrakk> \<Longrightarrow> dfull n (del (if_eq GREATER None k) r)"
    and "full (Suc n) (Branch2 l p r)"
    hence "dfull n (del k (Branch2 l p r))"
     apply clarsimp
     apply (cases n)
      apply (cases k)
       apply simp
      apply (simp split: ord.split)
     apply simp
     apply (subst del_extra_simps, force)
     (* This should work, but it is way too slow!
     apply (force split: ord.split option.split bool.split tree23.split) *)
     apply (simp | rule dfull_case_intros)+
     done
  } note A = this
  { fix n :: "nat" and p q :: "key \<times> 'a" and l m r :: "'a tree23" and k
    assume "\<And>n. \<lbrakk>compare k q = LESS; compare k p = LESS; full (Suc n) l\<rbrakk> \<Longrightarrow> dfull n (del k l)"
    and "\<And>n. \<lbrakk>compare k q = LESS; compare k p = EQUAL; full (Suc n) m\<rbrakk> \<Longrightarrow> dfull n (del (if_eq EQUAL None k) m)"
    and "\<And>n. \<lbrakk>compare k q = LESS; compare k p = GREATER; full (Suc n) m\<rbrakk> \<Longrightarrow> dfull n (del (if_eq GREATER None k) m)"
    and "\<And>n. \<lbrakk>compare k q = EQUAL; full (Suc n) r\<rbrakk> \<Longrightarrow> dfull n (del (if_eq EQUAL None k) r)"
    and "\<And>n. \<lbrakk>compare k q = GREATER; full (Suc n) r\<rbrakk> \<Longrightarrow> dfull n (del (if_eq GREATER None k) r)"
    and "full (Suc n) (Branch3 l p m q r)"
    hence "dfull n (del k (Branch3 l p m q r))"
     apply clarsimp
     apply (cases n)
      apply (cases k)
       apply simp
      apply (simp split: ord.split)
     apply simp
     apply (subst del_extra_simps, force)
     apply (simp | rule dfull_case_intros)+
     done
  } note B = this
  show "full (Suc n) t \<Longrightarrow> dfull n (del k t)"
  proof (induct k t arbitrary: n rule: del.induct, goal_cases)
    case (1 k n)
    thus "dfull n (del (Some k) Empty)" by simp
  next
    case (2 p n)
    thus "dfull n (del None (Branch2 Empty p Empty))" by simp
  next
    case (3 p q n)
    thus "dfull n (del None (Branch3 Empty p Empty q Empty))" by simp
  next
    case (4 v p n)
    thus "dfull n (del (Some v) (Branch2 Empty p Empty))"
      by (simp split: ord.split)
  next
    case (5 v p q n)
    thus "dfull n (del (Some v) (Branch3 Empty p Empty q Empty))"
      by (simp split: ord.split)
  next
    case (26 n)
    thus ?case by simp
  qed (fact A | fact B)+
qed

lemma bal_del0: "bal t \<Longrightarrow> bal (del0 k t)"
unfolding bal_iff_full del0_def
apply (erule exE)
apply (case_tac n, simp, simp)
apply (frule dfull_del [where k="Some k"])
apply (cases "del (Some k) t", force)
apply (rename_tac a, case_tac "a", rename_tac b t', case_tac "b", auto)
done

text\<open>This is a little test harness and should be commented out once the
above functions have been proved correct.\<close>

datatype 'a act = Add int 'a | Del int

fun exec where
"exec [] t = t" |
"exec (Add k x # as) t = exec as (add0 k x t)" |
"exec (Del k # as) t = exec as (del0 k t)"

text\<open>Some quick checks:\<close>

lemma bal_exec: "bal t \<Longrightarrow> bal (exec as t)"
  by (induct as t arbitrary: t rule: exec.induct,
    simp_all add: bal_add0 bal_del0)

lemma "bal(exec as Empty)"
  by (simp add: bal_exec)

lemma "ord0(exec as Empty)"
quickcheck
oops

end
