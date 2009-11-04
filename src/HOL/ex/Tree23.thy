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

types key = int -- {*for simplicity, should be a type class*}

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

fun height :: "'a tree23 \<Rightarrow> nat" where
"height Empty = 0" |
"height (Branch2 l _ r) = Suc(max (height l) (height r))" |
"height (Branch3 l _ m _ r) = Suc(max (height l) (max (height m) (height r)))"

text{* Is a tree balanced? *}
fun bal :: "'a tree23 \<Rightarrow> bool" where
"bal Empty = True" |
"bal (Branch2 l _ r) = (bal l & bal r & height l = height r)" |
"bal (Branch3 l _ m _ r) = (bal l & bal m & bal r & height l = height m & height m = height r)"

text{* This is a little test harness and should be commented out once the
above functions have been proved correct. *}

datatype 'a act = Add int 'a | Del int

fun exec where
"exec [] t = t" |
"exec (Add k x # as) t = exec as (add0 k x t)" |
"exec (Del k # as) t = exec as (del0 k t)"

text{* Some quick checks: *}

lemma "ord0(exec as Empty)"
quickcheck
oops

lemma "bal(exec as Empty)"
quickcheck
oops

end