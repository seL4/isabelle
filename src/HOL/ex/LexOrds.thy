(* Title:       HOL/ex/LexOrds.thy
   ID:
   Author:      Lukas Bulwahn, TU Muenchen

Examples for functions whose termination is proven by lexicographic order.
*)
 
theory LexOrds
imports Main
begin

use "~~/src/HOL/Tools/function_package/sum_tools.ML"
use "~~/src/HOL/Tools/function_package/fundef_common.ML"
use "~~/src/HOL/Tools/function_package/fundef_lib.ML"
use "~~/src/HOL/Tools/function_package/inductive_wrap.ML"
use "~~/src/HOL/Tools/function_package/context_tree.ML"
(* use "~~/src/HOL/Tools/function_package/fundef_tailrec.ML"*)
use "~~/src/HOL/Tools/function_package/fundef_prep.ML"
use "~~/src/HOL/Tools/function_package/fundef_proof.ML"
use "~~/src/HOL/Tools/function_package/termination.ML"
use "~~/src/HOL/Tools/function_package/mutual.ML"
use "~~/src/HOL/Tools/function_package/pattern_split.ML"
use "~~/src/HOL/Tools/function_package/auto_term.ML"
use "~~/src/HOL/Tools/function_package/fundef_package.ML"
use "~~/src/HOL/Tools/function_package/lexicographic_order.ML"
use "~~/src/HOL/Tools/function_package/fundef_datatype.ML"


setup FundefPackage.setup
setup LexicographicOrder.setup
setup FundefDatatype.setup

lemmas [fundef_cong] = 
  let_cong if_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong
  map_cong


subsection {* Trivial examples *}

fun f :: "nat \<Rightarrow> nat"
where
"f n = n"

fun g :: "nat \<Rightarrow> nat"
where 
  "g 0 = 0"
  "g (Suc n) = Suc (g n)"


subsection {* Examples on natural numbers *}

fun bin :: "(nat * nat) \<Rightarrow> nat"
where
  "bin (0, 0) = 1"
  "bin (Suc n, 0) = 0"
  "bin (0, Suc m) = 0"
  "bin (Suc n, Suc m) = bin (n, m) + bin (Suc n, m)"


fun t :: "(nat * nat) \<Rightarrow> nat"
where
  "t (0,n) = 0"
  "t (n,0) = 0"
  "t (Suc n, Suc m) = (if (n mod 2 = 0) then (t (Suc n, m)) else (t (n, Suc m)))" 


function h :: "(nat * nat) * (nat * nat) \<Rightarrow> nat"
where
  "h ((0,0),(0,0)) = 0"
  "h ((Suc z, y), (u,v)) = h((z, y), (u, v))" (* z is descending *)
  "h ((0, Suc y), (u,v)) = h((1, y), (u, v))" (* y is descending *)
  "h ((0,0), (Suc u, v)) = h((1, 1), (u, v))" (* u is descending *)
  "h ((0,0), (0, Suc v)) = h ((1,1), (1,v))" (*  v is descending *)
by (pat_completeness, auto)

termination by lexicographic_order

lemma[simp]: "size x = x"
apply (induct x) apply simp_all done

fun gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd2 x 0 = x"
  "gcd2 0 y = y"
  "gcd2 (Suc x) (Suc y) = (if x < y then gcd2 (Suc x) (y - x)
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


subsection {* Examples with mutual recursion *}

fun evn od :: "nat \<Rightarrow> bool"
where
  "evn 0 = True"
| "od 0 = False"
| "evn (Suc n) = od n"
| "od (Suc n) = evn n"


fun
 evn2 od2  :: "(nat * nat) \<Rightarrow> bool"
where
  "evn2 (0, n) = True"
  "evn2 (n, 0) = True"
  "od2 (0, n) = False"
  "od2 (n, 0) = False"
  "evn2 (Suc n, Suc m) = od2 (Suc n, m)"
  "od2 (Suc n, Suc m) = evn2 (n, Suc m)"


fun evn3 od3 :: "(nat * nat) \<Rightarrow> nat"
where
  "evn3 (0,n) = n"
  "od3 (0,n) = n"
  "evn3 (n,0) = n"
  "od3 (n,0) = n"
  "evn3 (Suc n, Suc m) = od3 (Suc m, n)"
  "od3 (Suc n, Suc m) = evn3 (Suc m, n) + od3(n, m)"


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
(*
lemma "i \<noteq> [] ==> sum_case (%x. size (fst x)) (%x. size (fst x)) (Inr (tl i, xa, i)) <  sum_case (%x. size (fst x)) (%x. size (fst x)) ( Inl (i, xa))"
apply simp
done
*)

lemma "i \<noteq> [] \<Longrightarrow> size (tl i) < size i"
apply simp
done

fun sizechange_f :: "'a list => 'a list => 'a list" and
sizechange_g :: "'a list => 'a list => 'a list => 'a list"
where
"sizechange_f i x = (if i=[] then x else sizechange_g (tl i) x i)"
"sizechange_g a b c = sizechange_f a (b @ c)"


fun
  prod :: "nat => nat => nat => nat" and
eprod :: "nat => nat => nat => nat" and
oprod :: "nat => nat => nat => nat"
where
"prod x y z = (if y mod 2 = 0 then eprod x y z else oprod x y z)"
"oprod x y z = eprod x (y - 1) (z+x)"
"eprod x y z = (if y=0 then z else prod (2*x) (y div 2) z)"


function (sequential)
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
  by pat_completeness auto

lemma [simp]: "size (x::nat) = x"
by (induct x) auto 

termination apply lexicographic_order done


subsection {*Examples for an unprovable termination *}

text {* If termination cannot be proven, the tactic gives further information about unprovable subgoals on the arguments *}

function noterm :: "(nat * nat) \<Rightarrow> nat"
where
  "noterm (a,b) = noterm(b,a)"
by pat_completeness auto
(* termination by apply lexicographic_order*)

function term_but_no_prove :: "nat * nat \<Rightarrow> nat"
where
  "term_but_no_prove (0,0) = 1"
  "term_but_no_prove (0, Suc b) = 0"
  "term_but_no_prove (Suc a, 0) = 0"
  "term_but_no_prove (Suc a, Suc b) = term_but_no_prove (b, a)"
by pat_completeness auto
(* termination by lexicographic_order *)

text{* The tactic distinguishes between N = not provable AND F = False *}
function no_proof :: "nat \<Rightarrow> nat"
where
  "no_proof m = no_proof (Suc m)"
by pat_completeness auto
(* termination by lexicographic_order *)

end