(* Title:       HOL/ex/Termination.thy
   Author:      Lukas Bulwahn, TU Muenchen
   Author:      Alexander Krauss, TU Muenchen
*)

header {* Examples and regression tests for automated termination proofs *}
 
theory Termination
imports Main "~~/src/HOL/Library/Multiset"
begin

subsection {* Manually giving termination relations using @{text relation} and
@{term measure} *}

function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "sum i N = (if i > N then 0 else i + sum (Suc i) N)"
by pat_completeness auto

termination by (relation "measure (\<lambda>(i,N). N + 1 - i)") auto

function foo :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "foo i N = (if i > N 
              then (if N = 0 then 0 else foo 0 (N - 1))
              else i + foo (Suc i) N)"
by pat_completeness auto

termination by (relation "measures [\<lambda>(i, N). N, \<lambda>(i,N). N + 1 - i]") auto


subsection {* @{text lexicographic_order}: Trivial examples *}

text {*
  The @{text fun} command uses the method @{text lexicographic_order} by default,
  so it is not explicitly invoked.
*}

fun identity :: "nat \<Rightarrow> nat"
where
  "identity n = n"

fun yaSuc :: "nat \<Rightarrow> nat"
where 
  "yaSuc 0 = 0"
| "yaSuc (Suc n) = Suc (yaSuc n)"


subsection {* Examples on natural numbers *}

fun bin :: "(nat * nat) \<Rightarrow> nat"
where
  "bin (0, 0) = 1"
| "bin (Suc n, 0) = 0"
| "bin (0, Suc m) = 0"
| "bin (Suc n, Suc m) = bin (n, m) + bin (Suc n, m)"


fun t :: "(nat * nat) \<Rightarrow> nat"
where
  "t (0,n) = 0"
| "t (n,0) = 0"
| "t (Suc n, Suc m) = (if (n mod 2 = 0) then (t (Suc n, m)) else (t (n, Suc m)))" 


fun k :: "(nat * nat) * (nat * nat) \<Rightarrow> nat"
where
  "k ((0,0),(0,0)) = 0"
| "k ((Suc z, y), (u,v)) = k((z, y), (u, v))" (* z is descending *)
| "k ((0, Suc y), (u,v)) = k((1, y), (u, v))" (* y is descending *)
| "k ((0,0), (Suc u, v)) = k((1, 1), (u, v))" (* u is descending *)
| "k ((0,0), (0, Suc v)) = k((1,1), (1,v))"   (* v is descending *)


fun gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd2 x 0 = x"
| "gcd2 0 y = y"
| "gcd2 (Suc x) (Suc y) = (if x < y then gcd2 (Suc x) (y - x)
                                    else gcd2 (x - y) (Suc y))"

fun ack :: "(nat * nat) \<Rightarrow> nat"
where
  "ack (0, m) = Suc m"
| "ack (Suc n, 0) = ack(n, 1)"
| "ack (Suc n, Suc m) = ack (n, ack (Suc n, m))"


fun greedy :: "nat * nat * nat * nat * nat => nat"
where
  "greedy (Suc a, Suc b, Suc c, Suc d, Suc e) =
  (if (a < 10) then greedy (Suc a, Suc b, c, d + 2, Suc e) else
  (if (a < 20) then greedy (Suc a, b, Suc c, d, Suc e) else
  (if (a < 30) then greedy (Suc a, b, Suc c, d, Suc e) else
  (if (a < 40) then greedy (Suc a, b, Suc c, d, Suc e) else
  (if (a < 50) then greedy (Suc a, b, Suc c, d, Suc e) else
  (if (a < 60) then greedy (a, Suc b, Suc c, d, Suc e) else
  (if (a < 70) then greedy (a, Suc b, Suc c, d, Suc e) else
  (if (a < 80) then greedy (a, Suc b, Suc c, d, Suc e) else
  (if (a < 90) then greedy (Suc a, Suc b, Suc c, d, e) else
  greedy (Suc a, Suc b, Suc c, d, e))))))))))"
| "greedy (a, b, c, d, e) = 0"


fun blowup :: "nat => nat => nat => nat => nat => nat => nat => nat => nat => nat"
where
  "blowup 0 0 0 0 0 0 0 0 0 = 0"
| "blowup 0 0 0 0 0 0 0 0 (Suc i) = Suc (blowup i i i i i i i i i)"
| "blowup 0 0 0 0 0 0 0 (Suc h) i = Suc (blowup h h h h h h h h i)"
| "blowup 0 0 0 0 0 0 (Suc g) h i = Suc (blowup g g g g g g g h i)"
| "blowup 0 0 0 0 0 (Suc f) g h i = Suc (blowup f f f f f f g h i)"
| "blowup 0 0 0 0 (Suc e) f g h i = Suc (blowup e e e e e f g h i)"
| "blowup 0 0 0 (Suc d) e f g h i = Suc (blowup d d d d e f g h i)"
| "blowup 0 0 (Suc c) d e f g h i = Suc (blowup c c c d e f g h i)"
| "blowup 0 (Suc b) c d e f g h i = Suc (blowup b b c d e f g h i)"
| "blowup (Suc a) b c d e f g h i = Suc (blowup a b c d e f g h i)"

  
subsection {* Simple examples with other datatypes than nat, e.g. trees and lists *}

datatype tree = Node | Branch tree tree

fun g_tree :: "tree * tree \<Rightarrow> tree"
where
  "g_tree (Node, Node) = Node"
| "g_tree (Node, Branch a b) = Branch Node (g_tree (a,b))"
| "g_tree (Branch a b, Node) = Branch (g_tree (a,Node)) b"
| "g_tree (Branch a b, Branch c d) = Branch (g_tree (a,c)) (g_tree (b,d))"


fun acklist :: "'a list * 'a list \<Rightarrow> 'a list"
where
  "acklist ([], m) = ((hd m)#m)"
|  "acklist (n#ns, []) = acklist (ns, [n])"
|  "acklist ((n#ns), (m#ms)) = acklist (ns, acklist ((n#ns), ms))"


subsection {* Examples with mutual recursion *}

fun evn od :: "nat \<Rightarrow> bool"
where
  "evn 0 = True"
| "od 0 = False"
| "evn (Suc n) = od (Suc n)"
| "od (Suc n) = evn n"


fun sizechange_f :: "'a list => 'a list => 'a list" and
sizechange_g :: "'a list => 'a list => 'a list => 'a list"
where
  "sizechange_f i x = (if i=[] then x else sizechange_g (tl i) x i)"
| "sizechange_g a b c = sizechange_f a (b @ c)"

fun
  pedal :: "nat => nat => nat => nat"
and
  coast :: "nat => nat => nat => nat"
where
  "pedal 0 m c = c"
| "pedal n 0 c = c"
| "pedal n m c =
     (if n < m then coast (n - 1) (m - 1) (c + m)
               else pedal (n - 1) m (c + m))"

| "coast n m c =
     (if n < m then coast n (m - 1) (c + n)
               else pedal n m (c + n))"



subsection {* Refined analysis: The @{text size_change} method *}

text {* Unsolvable for @{text lexicographic_order} *}

function fun1 :: "nat * nat \<Rightarrow> nat"
where
  "fun1 (0,0) = 1"
| "fun1 (0, Suc b) = 0"
| "fun1 (Suc a, 0) = 0"
| "fun1 (Suc a, Suc b) = fun1 (b, a)"
by pat_completeness auto
termination by size_change


text {* 
  @{text lexicographic_order} can do the following, but it is much slower. 
*}

function
  prod :: "nat => nat => nat => nat" and
  eprod :: "nat => nat => nat => nat" and
  oprod :: "nat => nat => nat => nat"
where
  "prod x y z = (if y mod 2 = 0 then eprod x y z else oprod x y z)"
| "oprod x y z = eprod x (y - 1) (z+x)"
| "eprod x y z = (if y=0 then z else prod (2*x) (y div 2) z)"
by pat_completeness auto
termination by size_change

text {* 
  Permutations of arguments:
*}

function perm :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "perm m n r = (if r > 0 then perm m (r - 1) n
                  else if n > 0 then perm r (n - 1) m
                  else m)"
by auto
termination by size_change

text {*
  Artificial examples and regression tests:
*}

function
  fun2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fun2 x y z =
      (if x > 1000 \<and> z > 0 then
           fun2 (min x y) y (z - 1)
       else if y > 0 \<and> x > 100 then
           fun2 x (y - 1) (2 * z)
       else if z > 0 then
           fun2 (min y (z - 1)) x x
       else
           0
      )"
by pat_completeness auto
termination by size_change -- {* requires Multiset *}

definition negate :: "int \<Rightarrow> int"
where "negate i = - i"

function fun3 :: "int => nat"
where
  "fun3 i =
  (if i < 0 then fun3 (negate i)
   else if i = 0 then 0
   else fun3 (i - 1))"
by (pat_completeness) auto
termination
  apply size_change
  apply (simp add: negate_def)
  apply size_change
  done


end
