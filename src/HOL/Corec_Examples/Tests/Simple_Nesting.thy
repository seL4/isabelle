(*  Title:      HOL/Corec_Examples/Tests/Simple_Nesting.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Tests "corec"'s parsing of map functions.
*)

section \<open>Tests "corec"'s Parsing of Map Functions\<close>

theory Simple_Nesting
imports "HOL-Library.BNF_Corec"
begin

subsection \<open>Corecursion via Map Functions\<close>

consts
  g :: 'a
  g' :: 'a
  g'' :: 'a
  h :: 'a
  h' :: 'a
  q :: 'a
  q' :: 'a

codatatype tree =
  Node nat "tree list"

(* a direct, intuitive way to define a function *)
corec k0 where
  "k0 x = Node (g x) (map (\<lambda>y. if q y then g' y else k0 (h' y :: 'a)) (h (x :: 'a) :: nat list))"

(* another way -- this one is perhaps less intuitive but more systematic *)
corec k0' where
  "k0' x = Node (g x) (map (\<lambda>z. case z of Inl t \<Rightarrow> t | Inr (x' :: 'a) \<Rightarrow> k0' x')
     (map (\<lambda>y. if q y then Inl (g' y) else Inr (h' y)) (h (x :: 'a) :: nat list)))"

(* more examples, same story *)

corec k1 :: "nat \<Rightarrow> tree" where
  "k1 x = Node (g x) (map (\<lambda>y. k1 (h' y)) (h x :: nat list))"

corec k1' :: "nat \<Rightarrow> tree" where
  "k1' x = Node (g x) (map (\<lambda>z. case z of Inl t \<Rightarrow> t | Inr x' \<Rightarrow> k1' x')
    (map (\<lambda>y. Inr (h' y)) (h x :: nat list)))"

corec k2 :: "nat \<Rightarrow> tree" where
  "k2 x = Node (g x) (map g' (h x :: nat list))"

corec k2' :: "nat \<Rightarrow> tree" where
  "k2' x = Node (g x) (map (\<lambda>z. case z of Inl t \<Rightarrow> t | Inr (x' :: nat) \<Rightarrow> k2' x')
     (map (\<lambda>y. Inl (g' y)) (h x :: nat list)))"

corec k3 :: "nat \<Rightarrow> tree" where
  "k3 x = Node (g x) (h x)"

corec k3' :: "nat \<Rightarrow> tree" where
  "k3' x = Node (g x) (map (\<lambda>z. case z of Inl t \<Rightarrow> t | Inr (x' :: nat) \<Rightarrow> k3' x')
    (map Inl (h x)))"


subsection \<open>Constructors instead of Maps\<close>

codatatype 'a y = Y 'a "'a y list"

corec hh where
  "hh a = Y a (map hh [a])"

corec k where
  "k a = Y a [k a, k undefined, k (a + a), undefined, k a]"

codatatype 'a x = X 'a "'a x option"

corec f where
  "f a = X a (map_option f (Some a))"

corec gg where
  "gg a = X a (Some (gg a))"


subsection \<open>Some Friends\<close>

codatatype u =
  U (lab: nat) (sub: "u list")

definition u_id :: "u \<Rightarrow> u" where "u_id u = u"

friend_of_corec u_id where
  "u_id u = U (lab u) (sub u)"
  by (simp add: u_id_def) transfer_prover

corec u_id_f :: "u \<Rightarrow> u" where
  "u_id_f u = u_id (U (lab u) (map u_id_f (sub u)))"

corec (friend) u_id_g :: "u \<Rightarrow> u" where
  "u_id_g u = U (lab u) (map (\<lambda>u'. u_id (u_id_g u')) (sub u))"

corec (friend) u_id_g' :: "u \<Rightarrow> u" where
  "u_id_g' u = U (lab u) (map (u_id o u_id_g') (sub u))"

corec (friend) u_id_g'' :: "u \<Rightarrow> u" where
  "u_id_g'' u = U (lab u) (map ((\<lambda>u'. u_id u') o u_id_g'') (sub u))"

corec u_id_h :: "u \<Rightarrow> u" where
  "u_id_h u = u_id (u_id (U (lab u) (map (\<lambda>u'. (u_id o u_id) (u_id (u_id (u_id_h u')))) (sub u))))"

corec u_id_h' :: "u \<Rightarrow> u" where
  "u_id_h' u = u_id (u_id (U (lab u) (map (u_id o u_id o u_id_h') (sub u))))"

corec u_id_h'' :: "u \<Rightarrow> u" where
  "u_id_h'' u = u_id (u_id (U (lab u) (map (u_id o (u_id o (\<lambda>u'. u_id u')) o u_id_h'') (sub u))))"

definition u_K :: "u \<Rightarrow> u \<Rightarrow> u" where "u_K u v = u"

friend_of_corec u_K where
  "u_K u v = U (lab u) (sub u)"
  by (simp add: u_K_def) transfer_prover

corec u_K_f :: "u \<Rightarrow> u" where
  "u_K_f u = u_K (U (lab u) (map u_K_f (sub u))) undefined"

corec (friend) u_K_g :: "u \<Rightarrow> u" where
  "u_K_g u = U (lab u) (map (\<lambda>u'. u_K (u_K_g u') undefined) (sub u))"

corec (friend) u_K_g' :: "u \<Rightarrow> u" where
  "u_K_g' u = U (lab u) (map ((\<lambda>u'. u_K u' undefined) o u_K_g') (sub u))"

corec (friend) u_K_g'' :: "u \<Rightarrow> u" where
  "u_K_g'' u = U (lab u) (map (u_K undefined o u_K_g'') (sub u))"

end
