(*  Title:      HOL/Corec_Examples/Tests/Merge_Poly.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Tests polymorphic merges.
*)

section \<open>Tests Polymorphic Merges\<close>

theory Merge_Poly
imports "HOL-Library.BNF_Corec"
begin

subsection \<open>A Monomorphic Example\<close>

codatatype r = R (rhd: nat) (rtl: r)

corec id_r :: "r \<Rightarrow> r" where
  "id_r r = R (rhd r) (id_r (rtl r))"

corec id_r' :: "r \<Rightarrow> r" where
  "id_r' r = R (rhd r) (id_r' (rtl r))"

corec id_r'' :: "r \<Rightarrow> r" where
  "id_r'' r = R (rhd r) (id_r'' (rtl r))"

consts
  f1 :: "r \<Rightarrow> r"
  f2 :: "r \<Rightarrow> r"
  f3 :: "r \<Rightarrow> r"

friend_of_corec f1 :: "r \<Rightarrow> r" where
  "f1 r = R (rhd r) (f1 (R (rhd r) (rtl r)))"
  sorry

friend_of_corec f2 :: "r \<Rightarrow> r" where
  "f2 r = R (rhd r) (f1 (f2 (rtl r)))"
  sorry

friend_of_corec f3 :: "r \<Rightarrow> r" where
  "f3 r = R (rhd r) (f3 (rtl r))"
  sorry

corec id_rx :: "r \<Rightarrow> r" where
  "id_rx r = f1 (f2 (f3 (R (rhd r) (id_rx (rtl r)))))"


subsection \<open>The Polymorphic Version\<close>

codatatype 'a s = S (shd: 'a) (stl: "'a s")

corec id_s :: "'a s \<Rightarrow> 'a s" where
  "id_s s = S (shd s) (id_s (stl s))"

corec id_s' :: "'b s \<Rightarrow> 'b s" where
  "id_s' s = S (shd s) (id_s' (stl s))"

corec id_s'' :: "'w s \<Rightarrow> 'w s" where
  "id_s'' s = S (shd s) (id_s'' (stl s))"

(* Registers polymorphic and nonpolymorphic friends in an alternating fashion. *)

consts
  g1 :: "'a \<Rightarrow> 'a s \<Rightarrow> 'a s"
  g2 :: "nat \<Rightarrow> nat s \<Rightarrow> nat s"
  g3 :: "'a \<Rightarrow> 'a s \<Rightarrow> 'a s"
  g4 :: "'a \<Rightarrow> 'a s \<Rightarrow> 'a s"
  g5 :: "nat \<Rightarrow> nat s \<Rightarrow> nat s"

friend_of_corec g3 :: "'b \<Rightarrow> 'b s \<Rightarrow> 'b s" where
  "g3 x s = S (shd s) (g3 x (stl s))"
  sorry

friend_of_corec g1 :: "'w \<Rightarrow> 'w s \<Rightarrow> 'w s" where
  "g1 x s = S (shd s) (g1 x (stl s))"
  sorry

friend_of_corec g2 :: "nat \<Rightarrow> nat s \<Rightarrow> nat s" where
  "g2 x s = S (shd s) (g1 x (stl s))"
  sorry

friend_of_corec g4 :: "'a \<Rightarrow> 'a s \<Rightarrow> 'a s" where
  "g4 x s = S (shd s) (g1 x (g4 x (stl s)))"
  sorry

friend_of_corec g5 :: "nat \<Rightarrow> nat s \<Rightarrow> nat s" where
  "g5 x s = S (shd s) (g2 x (g5 x (stl s)))"
  sorry

corec id_nat_s :: "nat s \<Rightarrow> nat s" where
  "id_nat_s s = g1 undefined (g2 undefined (g3 undefined (S (shd s) (id_nat_s (stl s)))))"

codatatype ('a, 'b) ABstream = ACons 'a (ABtl: "('a, 'b) ABstream") | BCons 'b (ABtl: "('a, 'b) ABstream")

consts
  h1 :: "('a, 'b) ABstream \<Rightarrow> ('a, 'b) ABstream"
  h2 :: "(nat, 'b) ABstream \<Rightarrow> (nat, 'b) ABstream"
  h3 :: "('a, nat) ABstream \<Rightarrow> ('a, nat) ABstream"
  h4 :: "('a :: zero, 'a) ABstream \<Rightarrow> ('a :: zero, 'a) ABstream"

friend_of_corec h1 where
  "h1 x = ACons undefined undefined" sorry

friend_of_corec h2 where
  "h2 x = (case x of
    ACons a t \<Rightarrow> ACons a (h1 (h2 t))
  | BCons b t \<Rightarrow> BCons b (h1 (h2 t)))"
  sorry

friend_of_corec h3 where
  "h3 x = (case x of
    ACons a t \<Rightarrow> ACons a (h1 (h3 t))
  | BCons b t \<Rightarrow> BCons b (h1 (h3 t)))"
  sorry

friend_of_corec h4 where
  "h4 x = (case x of
    ACons a t \<Rightarrow> ACons a (h1 (h4 t))
  | BCons b t \<Rightarrow> BCons b (h1 (h4 t)))"
  sorry

corec (friend) h5 where
  "h5 x = (case x of
    ACons a t \<Rightarrow> ACons a (h1 (h2 (h3 (h4 (h5 t)))))
  | BCons b t \<Rightarrow> BCons b (h1 (h2 (h3 (h4 (h5 t))))))"

corec (friend) h6 :: "(nat, nat) ABstream \<Rightarrow> (nat, nat) ABstream" where
  "h6 x = (case x of
    ACons a t \<Rightarrow> ACons a (h6 (h1 (h2 (h3 (h4 (h5 (h6 t)))))))
  | BCons b t \<Rightarrow> BCons b (h1 (h2 (h3 (h4 (h5 (h6 t)))))))"

end
