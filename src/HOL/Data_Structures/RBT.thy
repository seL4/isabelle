(* Author: Tobias Nipkow *)

section \<open>Red-Black Trees\<close>

theory RBT
imports Tree2
begin

datatype color = Red | Black

type_synonym 'a rbt = "('a,color)tree"

abbreviation R where "R l a r \<equiv> Node Red l a r"
abbreviation B where "B l a r \<equiv> Node Black l a r"

fun bal :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
(* The first line is superfluous; it merely speeds up pattern compilation *)
"bal (R t1 a1 t2) a2 (R t3 a3 t4) = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"bal (R (R t1 a1 t2) a2 t3) a3 t4 = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"bal (R t1 a1 (R t2 a2 t3)) a3 t4 = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"bal t1 a1 (R t2 a2 (R t3 a3 t4)) = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"bal t1 a1 (R (R t2 a2 t3) a3 t4) = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"bal t1 a t2 = B t1 a t2"

fun paint :: "color \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"paint c Leaf = Leaf" |
"paint c (Node _ l a r) = Node c l a r"

fun balL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"balL (R t1 x t2) y t3 = R (B t1 x t2) y t3" |
"balL bl x (B t1 y t2) = bal bl x (R t1 y t2)" |
"balL bl x (R (B t1 y t2) z t3) = R (B bl x t1) y (bal t2 z (paint Red t3))" |
"balL t1 x t2 = R t1 x t2"

fun balR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"balR t1 x (R t2 y t3) = R t1 x (B t2 y t3)" |
"balR (B t1 x t2) y t3 = bal (R t1 x t2) y t3" |
"balR (R t1 x (B t2 y t3)) z t4 = R (bal (paint Red t1) x t2) y (B t3 z t4)" |
"balR t1 x t2 = R t1 x t2"

fun combine :: "'a rbt \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"combine Leaf t = t" |
"combine t Leaf = t" |
"combine (R t1 a t2) (R t3 c t4) =
  (case combine t2 t3 of
     R u2 b u3 \<Rightarrow> (R (R t1 a u2) b (R u3 c t4)) |
     t23 \<Rightarrow> R t1 a (R t23 c t4))" |
"combine (B t1 a t2) (B t3 c t4) =
  (case combine t2 t3 of
     R t2' b t3' \<Rightarrow> R (B t1 a t2') b (B t3' c t4) |
     t23 \<Rightarrow> balL t1 a (B t23 c t4))" |
"combine t1 (R t2 a t3) = R (combine t1 t2) a t3" |
"combine (R t1 a t2) t3 = R t1 a (combine t2 t3)" 

end
