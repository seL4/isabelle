(*  Title:      HOL/Corec_Examples/Tests/Misc_Mono.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Miscellaneous monomorphic examples.
*)

section \<open>Miscellaneous Monomorphic Examples\<close>

theory Misc_Mono
imports "HOL-Library.BNF_Corec"
begin

codatatype T0 =
  C1 (lab: nat) (tl11: T0) (tl12: T0)
| C2 (lab: nat) (tl2: T0)
| C3 (tl3: "T0 list")

codatatype stream =
  S (hd: nat) (tl: stream)

corec (friend) ff where
  "ff x = S 0 (ff (ff x))"

corec test0 where
  "test0 x y = (case (x, y) of
  (S a1 s1, S a2 s2) \<Rightarrow> S (a1 + a2) (test0 s1 s2))"

friend_of_corec test0 where
  "test0 x y = (case (x, y) of
  (S a1 s1, S a2 s2) \<Rightarrow> S (a1 + a2) (test0 s1 s2))"
   apply (rule test0.code)
  apply transfer_prover
  done

corec test01 where
  "test01 x y = C2 (lab x + lab y) (test01 (tl2 x) (tl2 y))"

friend_of_corec test01 where
  "test01 x y = C2 (lab x + lab y) (test01 (tl2 x) (tl2 y))"
   apply (rule test01.code)
  sorry (* not parametric *)

corec test02 where
  "test02 x y = C2 (lab x * lab y) (test01 (test02 x (tl2 y)) (test02 (tl2 x) y))"

friend_of_corec test02 where
  "test02 x y = C2 (lab x * lab y) (test01 (test02 x (tl2 y)) (test02 (tl2 x) y))"
   apply (rule test02.code)
  sorry (* not parametric *)

corec test03 where
  "test03 x = C2 (lab x) (C2 (lab x) (test02 (test03 (tl2 x)) (test03 (tl2 x))))"

friend_of_corec test03 where
  "test03 x = C2 (lab x) (C2 (lab x) (test02 (test03 (tl2 x)) (test03 (tl2 x))))"
   apply (rule test03.code)
  sorry (* not parametric *)

corec (friend) test04a where
  "test04a x = (case x of C1 a t1 t2 \<Rightarrow> C1 (a * a) (test04a t1) (test04a t2) | C2 a t \<Rightarrow> C2 (a * a) (test04a t) | C3 l \<Rightarrow> C3 l)"

corec test04 where
  "test04 x = (case x of C1 a t1 t2 \<Rightarrow> C1 (a * a) (test04 t1) (test04 t2) | C2 a t \<Rightarrow> C2 (a * a) (test04 t) | C3 l \<Rightarrow> C3 l)"

friend_of_corec test04 where
  "test04 x = (case x of C1 a t1 t2 \<Rightarrow> C1 (a * a) (test04 t1) (test04 t2) | C2 a t \<Rightarrow> C2 (a * a) (test04 t) | C3 l \<Rightarrow> C3 l)"
   apply (rule test04.code)
  apply transfer_prover
  done

corec test05 where
  "test05 x y = (case (x, y) of
  (C1 a t11 t12, C1 b t21 t22) \<Rightarrow> C1 (a + b) (test05 t11 t21) (test05 t12 t22)
| (C1 a t11 _, C2 b t2) \<Rightarrow> C2 (a + b) (test05 t11 t2)
| (C2 a t1, C1 b _ t22) \<Rightarrow> C2 (a + b) (test05 t1 t22)
| (C2 a t1, C2 b t2) \<Rightarrow> C2 (a + b) (test05 t1 t2)
| (_, _) \<Rightarrow> C3 [])"

friend_of_corec test05 where
  "test05 x y = (case (x, y) of
  (C1 a t11 t12, C1 b t21 t22) \<Rightarrow> C1 (a + b) (test05 t11 t21) (test05 t12 t22)
| (C1 a t11 _, C2 b t2) \<Rightarrow> C2 (a + b) (test05 t11 t2)
| (C2 a t1, C1 b _ t22) \<Rightarrow> C2 (a + b) (test05 t1 t22)
| (C2 a t1, C2 b t2) \<Rightarrow> C2 (a + b) (test05 t1 t2)
| (_, _) \<Rightarrow> C3 [])"
   apply (rule test05.code)
  apply transfer_prover
  done

corec test06 :: "T0 \<Rightarrow> T0" where
  "test06 x =
  (if \<not> is_C1 x then
    let tail = tl2 x in
    C1 (lab x) (test06 tail) tail
  else
    C2 (lab x) (test06 (tl12 x)))"

friend_of_corec test06 :: "T0 \<Rightarrow> T0" where
  "test06 x =
  (if \<not> is_C1 x then
    let tail = tl2 x in
    C1 (lab x) (test06 tail) tail
  else
    C2 (lab x) (test06 (tl12 x)))"
   apply (rule test06.code)
  sorry (* not parametric *)

corec test07 where
  "test07 xs = C3 (map (\<lambda>x. test07 (tl3 x)) xs)"

friend_of_corec test07 where
  "test07 xs = C3 (map (\<lambda>x. test07 (tl3 x)) xs)"
   apply (rule test07.code)
  sorry (* not parametric *)

corec test08 where
  "test08 xs = (case xs of
    [] \<Rightarrow> C2 0 (test08 [])
  | T # r \<Rightarrow> C1 1 (test08 r) T)"

friend_of_corec test08 where
  "test08 xs = (case xs of
    [] \<Rightarrow> C2 0 (test08 [])
  | T # r \<Rightarrow> C1 1 (test08 r) T)"
   apply (rule test08.code)
  apply transfer_prover
  done

corec test09 where
  "test09 xs = test08 [case xs of
    [] \<Rightarrow> C2 0 (test09 [])
  | (C1 n T1 T2) # r \<Rightarrow> C1 n (test09 (T1 # r)) (test09 (T2 # r))
  | _ # r \<Rightarrow> C3 [test09 r]]"

friend_of_corec test09 where
  "test09 xs = (case xs of
    [] \<Rightarrow> C2 0 (test09 [])
  | (C1 n T1 T2) # r \<Rightarrow> C1 n (test09 (T1 # r)) (test09 (T2 # r))
  | _ # r \<Rightarrow> C3 [test09 r])"
   defer
   apply transfer_prover
  sorry (* not sure the specifications are equal *)

codatatype tree =
  Node (node: int) (branches: "tree list")

consts integerize_tree_list :: "'a list \<Rightarrow> int"

lemma integerize_tree_list_transfer[transfer_rule]:
  "rel_fun (list_all2 R) op = integerize_tree_list integerize_tree_list"
  sorry

corec (friend) f10a where
  "f10a x y = Node
  (integerize_tree_list (branches x) + integerize_tree_list (branches y))
  (map (\<lambda>(x, y). f10a x y) (zip (branches x) (branches y)))"

corec f10 where
  "f10 x y = Node
  (integerize_tree_list (branches x) + integerize_tree_list (branches y))
  (map (\<lambda>(x, y). f10 x y) (zip (branches x) (branches y)))"

friend_of_corec f10 where
  "f10 x y = Node
  (integerize_tree_list (branches x) + integerize_tree_list (branches y))
  (map (\<lambda>(x, y). f10 x y) (zip (branches x) (branches y)))"
     apply (rule f10.code)
    by transfer_prover+

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

corec f14 :: "tree option \<Rightarrow> tree" where
  "f14 t_opt = Node 0
    (case map_option branches t_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f14 o Some) ts)"

friend_of_corec f14 where
  "f14 t_opt = Node 0
    (case map_option branches t_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f14 o Some) ts)"
  sorry

corec f15 :: "tree list option \<Rightarrow> tree" where
  "f15 ts_opt = Node 0
    (case map_option (map branches) ts_opt of
      None \<Rightarrow> []
    | Some tss \<Rightarrow> map (f15 o Some) tss)"

friend_of_corec f15 where
  "f15 ts_opt = Node 0
    (case map_option (map branches) ts_opt of
      None \<Rightarrow> []
    | Some tss \<Rightarrow> map (f15 o Some) tss)"
    sorry

corec f16 :: "tree list option \<Rightarrow> tree" where
  "f16 ts_opt = Node 0
    (case ts_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f16 o Some o branches) ts)"

friend_of_corec f16 where
  "f16 ts_opt = Node 0
    (case ts_opt of
      None \<Rightarrow> []
    | Some ts \<Rightarrow> map (f16 o Some o branches) ts)"
    sorry

corec f17 :: "tree list option \<Rightarrow> tree" where
  "f17 ts_opt = Node 0 (case ts_opt of
    None \<Rightarrow> []
  | Some ts \<Rightarrow> [f17 (Some (map (List.hd o branches) ts))])"

(* not parametric
friend_of_corec f17 where
  "f17 ts_opt = Node 0 (case ts_opt of
    None \<Rightarrow> []
  | Some ts \<Rightarrow> [f17 (Some (map (List.hd o branches) ts))])"
  sorry
*)

corec f18 :: "tree \<Rightarrow> tree" where
  "f18 t = Node (node t) (map (f18 o f12) (branches t))"

friend_of_corec f18 :: "tree \<Rightarrow> tree" where
  "f18 t = Node (node t) (map (f18 o f12) (branches t))"
  sorry

corec f19 :: "tree \<Rightarrow> tree" where
  "f19 t = Node (node t) (map (%f. f [t]) (map f13 [1, 2, 3]))"

friend_of_corec f19 :: "tree \<Rightarrow> tree" where
  "f19 t = Node (node t) (map (%f. f [t]) (map f13 [1, 2, 3]))"
  sorry

datatype ('a, 'b, 'c) h = H1 (h_a: 'a) (h_tail: "('a, 'b, 'c) h") | H2 (h_b: 'b) (h_c: 'c) (h_tail: "('a, 'b, 'c) h") | H3

term "map_h (map_option f12) (%n. n) f12"

corec f20 :: "(tree option, int, tree) h \<Rightarrow> tree \<Rightarrow> tree" where
  "f20 x y = Node (node y) (case (map_h (map_option f12) (%n. n) f12 x) of
    H1 None r \<Rightarrow> (f20 r y) # (branches y)
  | H1 (Some t) r \<Rightarrow> (f20 r t) # (branches y)
  | H2 n t r \<Rightarrow> (f20 r (Node n [])) # (branches y)
  | H3 \<Rightarrow> branches y)"

friend_of_corec f20 where
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

corec f22 :: "('a \<Rightarrow> tree) \<Rightarrow> 'a list \<Rightarrow> tree" where
  "f22 f x = Node 0 (map f x)"

friend_of_corec f22:: "(nat \<Rightarrow> tree) \<Rightarrow> nat list \<Rightarrow> tree"  where
  "f22 f x = Node 0 (map f x)"
    sorry

corec f23 where
  "f23 xh = Node 0
    (if is_H1 xh then
      (f23 (h_tail xh)) # (branches (h_a xh))
    else if is_H1 xh then
      (f23 (h_tail xh)) # (h_c xh) # (branches (h_b xh))
    else
      [])"

friend_of_corec f23 where
  "f23 xh = Node 0
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

friend_of_corec f24 :: "(nat \<Rightarrow> tree list, int, int \<Rightarrow> tree list) h \<Rightarrow> tree" where
  "f24 xh =
    (if is_H1 xh then
      Node 0 ((f24 (h_tail xh)) # (h_a xh 0))
    else if is_H2 xh then
      Node (h_b xh) ((f24 (h_tail xh)) # (h_c xh 0))
    else
      Node 0 [])"
  sorry

corec f25 where
  "f25 x = Node (node x) (map f25 ((id branches) x))"

codatatype ('a, 'b) y_type =
  Y (lab: "'a \<Rightarrow> 'b") (y_tail: "('a, 'b) y_type")

corec f26 :: "(int, tree) y_type \<Rightarrow> tree \<Rightarrow> tree" where
  "f26 y x = (case map_y_type f12 y of
  Y f y' \<Rightarrow> Node (node x) ((f (node x)) # (map (f26 y') (branches x))))"

friend_of_corec f26 where
  "f26 y x = (case map_y_type f12 y of
  Y f y' \<Rightarrow> Node (node x) ((f (node x)) # (map (f26 y') (branches x))))"
  sorry

consts int_of_list :: "'a list \<Rightarrow> int"

corec f27 :: "(int, tree) y_type \<Rightarrow> tree \<Rightarrow> tree" where
  "f27 y x = Node (int_of_list (map (f26 (y_tail y)) (branches x))) [lab y (node x)]"

friend_of_corec f27 :: "(int, tree) y_type \<Rightarrow> tree \<Rightarrow> tree" where
  "f27 y x = Node (int_of_list (map (f26 (y_tail y)) (branches x))) [lab y (node x)]"
  sorry

corec f28 :: "(tree option list, (int \<Rightarrow> int) \<Rightarrow> int list \<Rightarrow> tree, tree) h \<Rightarrow> tree" where
  "f28 xh = (case xh of
    H3 \<Rightarrow> Node 0 []
  | H1 l r \<Rightarrow> Node 0 ((f28 r) # map the (filter (%opt. case opt of None \<Rightarrow> False | Some _ \<Rightarrow> True) l))
  | H2 f t r \<Rightarrow> Node (node t) (map (%t. f id [node t]) (branches t)))"

codatatype llist =
  LNil | LCons (head: nat) (tail: llist)

inductive llist_in where
  "llist_in (LCons x xs) x"
| "llist_in xs y \<Longrightarrow> llist_in (LCons x xs) y"

abbreviation "lset xs \<equiv> {x. llist_in xs x}"

corecursive lfilter where
  "lfilter P xs = (if \<forall> x \<in> lset xs. \<not> P x then
    LNil
    else if P (head xs) then
      LCons (head xs) (lfilter P (tail xs))
    else
      lfilter P (tail xs))"
proof (relation "measure (\<lambda>(P, xs). LEAST n. P (head ((tail ^^ n) xs)))", rule wf_measure, clarsimp)
  fix P xs x
  assume "llist_in xs x" "P x" "\<not> P (head xs)"
  from this(1,2) obtain a where "P (head ((tail ^^ a) xs))"
    by (atomize_elim, induct xs x rule: llist_in.induct) (auto simp: funpow_Suc_right
      simp del: funpow.simps(2) intro: exI[of _ 0] exI[of _ "Suc i" for i])
  with \<open>\<not> P (head xs)\<close>
    have "(LEAST n. P (head ((tail ^^ n) xs))) = Suc (LEAST n. P (head ((tail ^^ Suc n) xs)))"
    by (intro Least_Suc) auto
  then show "(LEAST n. P (head ((tail ^^ n) (tail xs)))) < (LEAST n. P (head ((tail ^^ n) xs)))"
    by (simp add: funpow_swap1[of tail])
qed

codatatype Stream =
  SCons (head: nat) (tail: Stream)

corec map_Stream where
  "map_Stream f s = SCons (f (head s)) (map_Stream f (tail s))"

friend_of_corec map_Stream where
  "map_Stream f s = SCons (f (head s)) (map_Stream f (tail s))"
  sorry

corec f29 where
  "f29 f ll = SCons (head ll) (f29 f (map_Stream f (tail ll)))"

friend_of_corec f29 where
  "f29 f ll = SCons (head ll) (f29 f (map_Stream f (tail ll)))"
  sorry

corec f30 where
  "f30 n m = (if n = 0 then SCons m (f30 m m) else f30 (n - 1) (n * m))"

corec f31 :: "llist \<Rightarrow> llist" where
  "f31 x = (if x = LNil then LCons undefined (f31 undefined) else LCons undefined undefined)"

friend_of_corec f31 where
  "f31 x = (if x = LNil then LCons undefined (f31 undefined) else LCons undefined undefined)"
  sorry

corec f32 :: "tree \<Rightarrow> tree" where
  "f32 t = Node (node t) (map ((\<lambda>t'. f18  t') o f32) (branches t))"

corec f33 :: "tree \<Rightarrow> tree" where
  "f33 t = f18 (f18 (Node (node t) (map (\<lambda>t'. (f18 o f18) (f18 (f18 (f33 t')))) (branches t))))"

corec f34 :: "tree \<Rightarrow> tree" where
  "f34 t = f18 (f18 (Node (node t) (map (f18 o f18 o f34) (branches t))))"

corec f35 :: "tree \<Rightarrow> tree" where
  "f35 t = f18 (f18 (Node (node t) (map (f18 o (f18 o (\<lambda>t'. f18 t')) o f35) (branches t))))"

corec f37 :: "int \<Rightarrow> tree list \<Rightarrow> tree option \<Rightarrow> nat \<Rightarrow> tree"  where
  "f37 a x1 = undefined a x1"

end
