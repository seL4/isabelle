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
"baliL (R (R t1 a t2) b t3) c t4 = R (B t1 a t2) b (B t3 c t4)" |
"baliL (R t1 a (R t2 b t3)) c t4 = R (B t1 a t2) b (B t3 c t4)" |
"baliL t1 a t2 = B t1 a t2"

fun baliR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baliR t1 a (R t2 b (R t3 c t4)) = R (B t1 a t2) b (B t3 c t4)" |
"baliR t1 a (R (R t2 b t3) c t4) = R (B t1 a t2) b (B t3 c t4)" |
"baliR t1 a t2 = B t1 a t2"

fun paint :: "color \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"paint c Leaf = Leaf" |
"paint c (Node l a _ r) = Node l a c r"

fun baldL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baldL (R t1 a t2) b t3 = R (B t1 a t2) b t3" |
"baldL bl a (B t1 b t2) = baliR bl a (R t1 b t2)" |
"baldL bl a (R (B t1 b t2) c t3) = R (B bl a t1) b (baliR t2 c (paint Red t3))" |
"baldL t1 a t2 = R t1 a t2"

fun baldR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baldR t1 a (R t2 b t3) = R t1 a (B t2 b t3)" |
"baldR (B t1 a t2) b t3 = baliL (R t1 a t2) b t3" |
"baldR (R t1 a (B t2 b t3)) c t4 = R (baliL (paint Red t1) a t2) b (B t3 c t4)" |
"baldR t1 a t2 = R t1 a t2"

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
