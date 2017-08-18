(*  Title:      HOL/Corec_Examples/Tests/Misc_Poly.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Miscellaneous polymorphic examples.
*)

section \<open>Miscellaneous Polymorphic Examples\<close>

theory Misc_Poly
imports "HOL-Library.BNF_Corec"
begin

codatatype ('a, 'b) T0 =
  C1 (lab: "'a * 'b") (tl11: "('a, 'b) T0") (tl12: "('a, 'b) T0")
| C2 (lab: "'a * 'b") (tl2: "('a, 'b) T0")
| C3 (tl3: "('a, 'b) T0 list")

codatatype stream = S (hd: nat) (tl: stream)

corec test0 where
  "test0 x y = (case (x, y) of
  (S a1 s1, S a2 s2) \<Rightarrow> S (a1 + a2) (test0 s1 s2))"

friend_of_corec test0 where
  "test0 x y = (case (x, y) of
  (S a1 s1, S a2 s2) \<Rightarrow> S (a1 + a2) (test0 s1 s2))"
  sorry

corec test01 where
  "test01 x y = C2 (fst (lab x), snd (lab y)) (test01 (tl2 x) (tl2 y))"

friend_of_corec test01 :: "('a, 'b) T0 \<Rightarrow> ('a, 'b) T0 \<Rightarrow> ('a, 'b) T0" where
  "test01 x y = C2 (fst (lab x), snd (lab y)) (test01 (tl2 x) (tl2 y))"
  sorry

corec test02 where
  "test02 x y = C2 (fst (lab x), snd (lab y)) (test01 (test02 x (tl2 y)) (test02 (tl2 x) y))"

friend_of_corec test02 :: "('a, 'b) T0 \<Rightarrow> ('a, 'b) T0 \<Rightarrow> ('a, 'b) T0"  where
  "test02 x y = C2 (fst (lab x), snd (lab y)) (test01 (test02 x (tl2 y)) (test02 (tl2 x) y))"
  sorry

corec test03 where
  "test03 x = C2 (lab x) (C2 (lab x) (test02 x x))"

friend_of_corec test03 where
  "test03 x = C2 (lab x) (C2 (lab x) (test02 (test03 (tl2 x)) (test03 (tl2 x))))"
  sorry

corec test04 where
  "test04 x = (case x of C1 a t1 t2 \<Rightarrow> C1 a (test04 t1) (test04 t2) | C2 a t \<Rightarrow> C2 a (test04 t) | C3 l \<Rightarrow> C3 l)"

friend_of_corec test04 where
  "test04 x = (case x of C1 a t1 t2 \<Rightarrow> C1 a (test04 t1) (test04 t2) | C2 a t \<Rightarrow> C2 a (test04 t) | C3 l \<Rightarrow> C3 l)"
  sorry

corec test05 where
  "test05 x y = (case (x, y) of
  (C1 a t11 t12, C1 b t21 t22) \<Rightarrow> C1 (fst a, snd b) (test05 t11 t21) (test05 t12 t22)
| (C1 a t11 _, C2 b t2) \<Rightarrow> C2 (fst a, snd b) (test05 t11 t2)
| (C2 a t1, C1 b _ t22) \<Rightarrow> C2 (fst a, snd b) (test05 t1 t22)
| (C2 a t1, C2 b t2) \<Rightarrow> C2 (fst a, snd b) (test05 t1 t2)
| (_, _) \<Rightarrow> C3 [])"

friend_of_corec test05 :: "('a, 'b) T0 \<Rightarrow> ('a, 'b) T0 \<Rightarrow> ('a, 'b) T0" where
  "test05 x y = (case (x, y) of
  (C1 a t11 t12, C1 b t21 t22) \<Rightarrow> C1 (fst a, snd b) (test05 t11 t21) (test05 t12 t22)
| (C1 a t11 _, C2 b t2) \<Rightarrow> C2 (fst a, snd b) (test05 t11 t2)
| (C2 a t1, C1 b _ t22) \<Rightarrow> C2 (fst a, snd b) (test05 t1 t22)
| (C2 a t1, C2 b t2) \<Rightarrow> C2 (fst a, snd b) (test05 t1 t2)
| (_, _) \<Rightarrow> C3 [])"
  sorry

corec test06 where
  "test06 x =
  (if \<not> is_C1 x then
    let tail = tl2 x in
    C1 (lab x) (test06 tail) tail
  else
    C2 (lab x) (test06 (tl12 x)))"

friend_of_corec test06 where
  "test06 x =
  (if \<not> is_C1 x then
    let tail = tl2 x in
    C1 (lab x) (test06 tail) tail
  else
    C2 (lab x) (test06 (tl12 x)))"
    sorry

corec test07 where
  "test07 xs = C3 (map (\<lambda>x. test07 (tl3 x)) xs)"

friend_of_corec test07 :: "('a, 'b) T0 list \<Rightarrow> ('a, 'b) T0" where
  "test07 xs = C3 (map (\<lambda>x. test07 (tl3 x)) xs)"
  sorry

corec test08 where
  "test08 xs = (case xs of
    [] \<Rightarrow> C3 []
  | T # r \<Rightarrow> C1 (lab T) (test08 r) T)"

friend_of_corec test08 where
  "test08 xs = (case xs of
    [] \<Rightarrow> C3 []
  | T # r \<Rightarrow> C1 (lab T) (test08 r) T)"
  sorry

corec test09 where
  "test09 xs = (case xs of
    [] \<Rightarrow> C3 []
  | (C1 n T1 T2) # r \<Rightarrow> C1 n (test09 (T1 # r)) (test09 (T2 # r))
  | _ # r \<Rightarrow> C3 [test09 r])"

friend_of_corec test09 where
  "test09 xs = (case xs of
    [] \<Rightarrow> C3 []
  | (C1 n T1 T2) # r \<Rightarrow> C1 n (test09 (T1 # r)) (test09 (T2 # r))
  | _ # r \<Rightarrow> C3 [test09 r])"
  sorry

codatatype 'h tree =
  Node (node: 'h) (branches: "'h tree list")

consts integerize_list :: "'a list \<Rightarrow> int"

corec f10 where
  "f10 x y = Node
  (integerize_list (branches x) + integerize_list (branches y))
  (map (\<lambda>(x, y). f10 x y) (zip (branches x) (branches y)))"

friend_of_corec f10 :: "int tree \<Rightarrow> int tree \<Rightarrow> int tree" where
  "f10 x y = Node
  (integerize_list (branches x) + integerize_list (branches y))
  (map (\<lambda>(x, y). f10 x y) (zip (branches x) (branches y)))"
  sorry

codatatype llist =
  Nil | LCons llist

consts friend :: "llist \<Rightarrow> llist"

friend_of_corec friend where
  "friend x = Nil"
  sorry

corec f11 where
  "f11 x = (case friend x of Nil \<Rightarrow> Nil | LCons y \<Rightarrow> LCons (f11 y))"

corec f12 where
  "f12 t = Node (node t) (map f12 (branches t))"

friend_of_corec f12 where
  "f12 t = Node (node t) (map f12 (branches t))"
  sorry

corec f13 where
  "f13 n ts = Node n (map (%t. f13 (node t) (branches t)) ts)"

friend_of_corec f13 where
  "f13 n ts = Node n (map (%t. f13 (node t) (branches t)) ts)"
  sorry

corec f14 where
  "f14 t_opt = Node undefined
    (case map_option branches t_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f14 o Some) ts)"

friend_of_corec f14 :: "'a tree option \<Rightarrow> 'a tree" where
  "f14 t_opt = Node undefined
    (case map_option branches t_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f14 o Some) ts)"
  sorry

corec f15 where
  "f15 ts_opt = Node undefined
    (case map_option (map branches) ts_opt of
      None \<Rightarrow> []
    | Some tss \<Rightarrow> map (f15 o Some) tss)"

friend_of_corec f15 :: "'a tree list option \<Rightarrow> 'a tree" where
  "f15 ts_opt = Node undefined
    (case map_option (map branches) ts_opt of
      None \<Rightarrow> []
    | Some tss \<Rightarrow> map (f15 o Some) tss)"
    sorry

corec f16 where
  "f16 ts_opt = Node undefined
    (case ts_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f16 o Some o branches) ts)"

friend_of_corec f16 :: "'a tree list option \<Rightarrow> 'a tree" where
  "f16 ts_opt = Node undefined
    (case ts_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f16 o Some o branches) ts)"
    sorry

corec f18 :: "'a tree \<Rightarrow> 'a tree" where
  "f18 t = Node (node t) (map (f18 o f12) (branches t))"

friend_of_corec f18 :: "'z tree \<Rightarrow> 'z tree" where
  "f18 t = Node (node t) (map (f18 o f12) (branches t))"
  sorry

corec f19 where
  "f19 t = Node (node t) (map (%f. f [t]) (map f13 [undefined]))"

friend_of_corec f19 where
  "f19 t = Node (node t) (map (%f. f [t]) (map f13 [undefined]))"
  sorry

datatype ('a, 'b, 'c) h = H1 (h_a: 'a) (h_tail: "('a, 'b, 'c) h") | H2 (h_b: 'b) (h_c: 'c) (h_tail: "('a, 'b, 'c) h") | H3

term "map_h (map_option f12) (%n. n) f12"

corec f20 where
  "f20 x y = Node (node y) (case (map_h (map_option f12) (%n. n) f12 x) of
    H1 None r \<Rightarrow> (f20 r y) # (branches y)
  | H1 (Some t) r \<Rightarrow> (f20 r t) # (branches y)
  | H2 n t r \<Rightarrow> (f20 r (Node n [])) # (branches y)
  | H3 \<Rightarrow> branches y)"

friend_of_corec f20 :: "('a tree option, 'a, 'a tree) h \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "f20 x y = Node (node y) (case (map_h (map_option f12) (%n. n) f12 x) of
    H1 None r \<Rightarrow> (f20 r y) # (branches y)
  | H1 (Some t) r \<Rightarrow> (f20 r t) # (branches y)
  | H2 n t r \<Rightarrow> (f20 r (Node n [])) # (branches y)
  | H3 \<Rightarrow> branches y)"
  sorry

corec f21 where
  "f21 x xh =
  Node (node x) (case xh of
    H1 (Some a) yh \<Rightarrow> (f21 x (map_h (map_option (f20 yh)) id id yh)) # (branches a)
  | H1 None yh \<Rightarrow> [f21 x yh]
  | H2 b c yh \<Rightarrow> (f21 c (map_h id (%n. n + b) id yh)) # (branches x)
  | H3 \<Rightarrow> branches x)"

friend_of_corec f21 where
  "f21 x xh =
  Node (node x) (case xh of
    H1 (Some a) yh \<Rightarrow> (f21 x (map_h (map_option (f20 yh)) (%t. t) (%t. t) yh)) # (branches a)
  | H1 None yh \<Rightarrow> [f21 x yh]
  | H2 b c yh \<Rightarrow> (f21 c (map_h (%t. t) (%n. n + b) (%t. t) yh)) # (branches x)
  | H3 \<Rightarrow> branches x)"
  sorry

corec f22 :: "('a \<Rightarrow> 'h tree) \<Rightarrow> 'a list \<Rightarrow> 'h tree" where
  "f22 f x = Node undefined (map f x)"

friend_of_corec f22 :: "('h \<Rightarrow> 'h tree) \<Rightarrow> 'h list \<Rightarrow> 'h tree" where
  "f22 f x = Node undefined (map f x)"
  sorry

corec f23 where
  "f23 xh = Node undefined
    (if is_H1 xh then
      (f23 (h_tail xh)) # (branches (h_a xh))
    else if is_H1 xh then
      (f23 (h_tail xh)) # (h_c xh) # (branches (h_b xh))
    else
      [])"

friend_of_corec f23 where
  "f23 xh = Node undefined
    (if is_H1 xh then
      (f23 (h_tail xh)) # (branches (h_a xh))
    else if is_H1 xh then
      (f23 (h_tail xh)) # (h_c xh) # (branches (h_b xh))
    else
      [])"
  sorry

corec f24 where
  "f24 xh =
    (if is_H1 xh then
      Node 0 ((f24 (h_tail xh)) # (h_a xh 0))
    else if is_H2 xh then
      Node (h_b xh) ((f24 (h_tail xh)) # (h_c xh 0))
    else
      Node 0 [])"

friend_of_corec f24 :: "(('b :: {zero}) \<Rightarrow> 'b tree list, 'b, 'b \<Rightarrow> 'b tree list) h \<Rightarrow> 'b tree" where
  "f24 xh =
    (if is_H1 xh then
      Node 0 ((f24 (h_tail xh)) # (h_a xh 0))
    else if is_H2 xh then
      Node (h_b xh) ((f24 (h_tail xh)) # (h_c xh 0))
    else
      Node 0 [])"
  sorry

codatatype ('a, 'b, 'c) s =
  S (s1: 'a) (s2: 'b) (s3: 'c) (s4: "('a, 'b, 'c) s")

corec (friend) ga :: "('a, 'b, nat) s \<Rightarrow> _" where
  "ga s = S (s1 s) (s2 s) (s3 s) (s4 s)"

corec (friend) gb :: "('a, nat, 'b) s \<Rightarrow> _" where
  "gb s = S (s1 s) (s2 s) (s3 s) (s4 s)"

consts foo :: "('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"

corecursive (friend) gc :: "(nat, 'a, 'b) s \<Rightarrow> _" where
  "gc s = S (s1 s) (s2 s) (s3 s) (foo (undefined :: 'a \<Rightarrow> 'a) s)"
  sorry

end
