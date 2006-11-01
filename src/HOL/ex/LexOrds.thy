(* Title:       HOL/ex/LexOrds.thy
   ID:
   Author:      Lukas Bulwahn, TU Muenchen

Examples for functions whose termination is proven by lexicographic order.
*)
 
theory LexOrds
imports Main
begin

subsection {* Trivial examples *}

fun f :: "nat \<Rightarrow> nat"
where
"f n = n"

termination by lexicographic_order


fun g :: "nat \<Rightarrow> nat"
where 
  "g 0 = 0"
  "g (Suc n) = Suc (g n)"

termination by lexicographic_order


subsection {* Examples on natural numbers *}

fun bin :: "(nat * nat) \<Rightarrow> nat"
where
  "bin (0, 0) = 1"
  "bin (Suc n, 0) = 0"
  "bin (0, Suc m) = 0"
  "bin (Suc n, Suc m) = bin (n, m) + bin (Suc n, m)"

termination by lexicographic_order


fun t :: "(nat * nat) \<Rightarrow> nat"
where
  "t (0,n) = 0"
  "t (n,0) = 0"
  "t (Suc n, Suc m) = (if (n mod 2 = 0) then (t (Suc n, m)) else (t (n, Suc m)))" 

termination by lexicographic_order

function h :: "(nat * nat) * (nat * nat) \<Rightarrow> nat"
where
  "h ((0,0),(0,0)) = 0"
  "h ((Suc z, y), (u,v)) = h((z, y), (u, v))" (* z is descending *)
  "h ((0, Suc y), (u,v)) = h((1, y), (u, v))" (* y is descending *)
  "h ((0,0), (Suc u, v)) = h((1, 1), (u, v))" (* u is descending *)
  "h ((0,0), (0, Suc v)) = h ((1,1), (1,v))" (*  v is descending *)
by (pat_completeness, auto)

termination by lexicographic_order


fun gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd2 x 0 = x"
| "gcd2 0 y = y"
| "gcd2 (Suc x) (Suc y) = (if x < y then gcd2 (Suc x) (y - x)
                                    else gcd2 (x - y) (Suc y))"

termination by lexicographic_order


function ack :: "(nat * nat) \<Rightarrow> nat"
where
  "ack (0, m) = Suc m"
  "ack (Suc n, 0) = ack(n, 1)"
  "ack (Suc n, Suc m) = ack (n, ack (Suc n, m))"
by pat_completeness auto

termination by lexicographic_order

subsection {* Simple examples with other datatypes than nat, e.g. trees and lists *}

datatype tree = Node | Branch tree tree

fun g_tree :: "tree * tree \<Rightarrow> tree"
where
  "g_tree (Node, Node) = Node"
  "g_tree (Node, Branch a b) = Branch Node (g_tree (a,b))"
  "g_tree (Branch a b, Node) = Branch (g_tree (a,Node)) b"
  "g_tree (Branch a b, Branch c d) = Branch (g_tree (a,c)) (g_tree (b,d))"


termination by lexicographic_order


fun acklist :: "'a list * 'a list \<Rightarrow> 'a list"
where
  "acklist ([], m) = ((hd m)#m)"
|  "acklist (n#ns, []) = acklist (ns, [n])"
|  "acklist ((n#ns), (m#ms)) = acklist (ns, acklist ((n#ns), ms))"

termination by lexicographic_order


subsection {* Examples with mutual recursion *}

fun evn od :: "nat \<Rightarrow> bool"
where
  "evn 0 = True"
| "od 0 = False"
| "evn (Suc n) = od n"
| "od (Suc n) = evn n"

termination by lexicographic_order


fun
 evn2 od2  :: "(nat * nat) \<Rightarrow> bool"
where
  "evn2 (0, n) = True"
  "evn2 (n, 0) = True"
  "od2 (0, n) = False"
  "od2 (n, 0) = False"
  "evn2 (Suc n, Suc m) = od2 (Suc n, m)"
  "od2 (Suc n, Suc m) = evn2 (n, Suc m)"

termination by lexicographic_order


fun evn3 od3 :: "(nat * nat) \<Rightarrow> nat"
where
  "evn3 (0,n) = n"
  "od3 (0,n) = n"
  "evn3 (n,0) = n"
  "od3 (n,0) = n"
  "evn3 (Suc n, Suc m) = od3 (Suc m, n)"
  "od3 (Suc n, Suc m) = evn3 (Suc m, n) + od3(n, m)"

termination by lexicographic_order


fun div3r0 div3r1 div3r2 :: "(nat * nat) \<Rightarrow> bool"
where
  "div3r0 (0, 0) = True"
  "div3r1 (0, 0) = False"
  "div3r2 (0, 0) = False"
  "div3r0 (0, Suc m) = div3r2 (0, m)"
  "div3r1 (0, Suc m) = div3r0 (0, m)"
  "div3r2 (0, Suc m) = div3r1 (0, m)"
  "div3r0 (Suc n, 0) = div3r2 (n, 0)"
  "div3r1 (Suc n, 0) = div3r0 (n, 0)"
  "div3r2 (Suc n, 0) = div3r1 (n, 0)"
  "div3r1 (Suc n, Suc m) = div3r2 (n, m)"
  "div3r2 (Suc n, Suc m) = div3r0 (n, m)"
  "div3r0 (Suc n, Suc m) = div3r1 (n, m)"

termination by lexicographic_order


subsection {*Examples for an unprovable termination *}

text {* If termination cannot be proven, the tactic gives further information about unprovable subgoals on the arguments *}

fun noterm :: "(nat * nat) \<Rightarrow> nat"
where
  "noterm (a,b) = noterm(b,a)"

(* termination by apply lexicographic_order*)

fun term_but_no_prove :: "nat * nat \<Rightarrow> nat"
where
  "term_but_no_prove (0,0) = 1"
  "term_but_no_prove (0, Suc b) = 0"
  "term_but_no_prove (Suc a, 0) = 0"
  "term_but_no_prove (Suc a, Suc b) = term_but_no_prove (b, a)"

(* termination by lexicographic_order *)

text{* The tactic distinguishes between N = not provable AND F = False *}
fun no_proof :: "nat \<Rightarrow> nat"
where
  "no_proof m = no_proof (Suc m)"

(* termination by lexicographic_order *)

end