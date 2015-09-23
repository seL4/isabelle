(* Author: Tobias Nipkow *)

section \<open>Red-Black Tree\<close>

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

fun red :: "'a rbt \<Rightarrow> 'a rbt" where
"red Leaf = Leaf" |
"red (Node _ l a r) = R l a r"

fun balL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"balL (R t1 x t2) s t3 = R (B t1 x t2) s t3" |
"balL bl x (B t1 y t2) = bal bl x (R t1 y t2)" |
"balL bl x (R (B t1 y t2) z t3) = R (B bl x t1) y (bal t2 z (red t3))" |
"balL t1 x t2 = R t1 x t2"

fun balR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"balR t1 x (R t2 y t3) = R t1 x (B t2 y t3)" |
"balR (B t1 x t2) y bl = bal (R t1 x t2) y bl" |
"balR (R t1 x (B t2 y t3)) z bl = R (bal (red t1) x t2) y (B t3 z bl)" |
"balR t1 x t2 = R t1 x t2"

fun combine :: "'a rbt \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"combine Leaf t = t" |
"combine t Leaf = t" |
"combine (R a x b) (R c y d) = (case combine b c of
    R b2 z c2 \<Rightarrow> (R (R a x b2) z (R c2 y d)) |
    bc \<Rightarrow> R a x (R bc y d))" |
"combine (B t1 a t2) (B t3 c t4) = (case combine t2 t3 of
    R t2' b t3' \<Rightarrow> R (B t1 a t2') b (B t3' c t4) |
    t23 \<Rightarrow> balL t1 a (B t23 c t4))" |
"combine t1 (R t2 a t3) = R (combine t1 t2) a t3" |
"combine (R t1 a t2) t3 = R t1 a (combine t2 t3)" 

end
