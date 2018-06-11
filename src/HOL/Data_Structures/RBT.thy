(* Author: Tobias Nipkow *)

section \<open>Red-Black Trees\<close>

theory RBT
imports Tree2
begin

datatype color = Red | Black

type_synonym 'a rbt = "('a,color)tree"

abbreviation R where "R l a r \<equiv> Node l a Red r"
abbreviation B where "B l a r \<equiv> Node l a Black r"

fun baliL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baliL (R (R t1 a1 t2) a2 t3) a3 t4 = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"baliL (R t1 a1 (R t2 a2 t3)) a3 t4 = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"baliL t1 a t2 = B t1 a t2"

fun baliR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baliR t1 a1 (R t2 a2 (R t3 a3 t4)) = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"baliR t1 a1 (R (R t2 a2 t3) a3 t4) = R (B t1 a1 t2) a2 (B t3 a3 t4)" |
"baliR t1 a t2 = B t1 a t2"

fun paint :: "color \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"paint c Leaf = Leaf" |
"paint c (Node l a _ r) = Node l a c r"

fun baldL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baldL (R t1 x t2) y t3 = R (B t1 x t2) y t3" |
"baldL bl x (B t1 y t2) = baliR bl x (R t1 y t2)" |
"baldL bl x (R (B t1 y t2) z t3) = R (B bl x t1) y (baliR t2 z (paint Red t3))" |
"baldL t1 x t2 = R t1 x t2"

fun baldR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baldR t1 x (R t2 y t3) = R t1 x (B t2 y t3)" |
"baldR (B t1 x t2) y t3 = baliL (R t1 x t2) y t3" |
"baldR (R t1 x (B t2 y t3)) z t4 = R (baliL (paint Red t1) x t2) y (B t3 z t4)" |
"baldR t1 x t2 = R t1 x t2"

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
     t23 \<Rightarrow> baldL t1 a (B t23 c t4))" |
"combine t1 (R t2 a t3) = R (combine t1 t2) a t3" |
"combine (R t1 a t2) t3 = R t1 a (combine t2 t3)" 

end
