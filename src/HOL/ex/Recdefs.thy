(*  Title:      HOL/ex/Recdefs.thy
    ID:         $Id$
    Author:     Konrad Slind and Lawrence C Paulson
    Copyright   1996  University of Cambridge

Examples of recdef definitions.  Most, but not all, are handled automatically.
*)

header {* Examples of recdef definitions *}

theory Recdefs = Main:

consts fact :: "nat => nat"
recdef fact  less_than
  "fact x = (if x = 0 then 1 else x * fact (x - 1))"

consts Fact :: "nat => nat"
recdef Fact  less_than
  "Fact 0 = 1"
  "Fact (Suc x) = Fact x * Suc x"

consts map2 :: "('a => 'b => 'c) * 'a list * 'b list => 'c list"
recdef map2  "measure(\<lambda>(f, l1, l2). size l1)"
  "map2 (f, [], [])  = []"
  "map2 (f, h # t, []) = []"
  "map2 (f, h1 # t1, h2 # t2) = f h1 h2 # map2 (f, t1, t2)"

consts finiteRchain :: "('a => 'a => bool) * 'a list => bool"
recdef finiteRchain  "measure (\<lambda>(R, l). size l)"
  "finiteRchain(R,  []) = True"
  "finiteRchain(R, [x]) = True"
  "finiteRchain(R, x # y # rst) = (R x y \<and> finiteRchain (R, y # rst))"

text {* Not handled automatically: too complicated. *}
consts variant :: "nat * nat list => nat"
recdef (permissive) variant  "measure (\<lambda>(n::nat, ns). size (filter (\<lambda>y. n \<le> y) ns))"
  "variant (x, L) = (if x mem L then variant (Suc x, L) else x)"

consts gcd :: "nat * nat => nat"
recdef gcd  "measure (\<lambda>(x, y). x + y)"
  "gcd (0, y) = y"
  "gcd (Suc x, 0) = Suc x"
  "gcd (Suc x, Suc y) =
    (if y \<le> x then gcd (x - y, Suc y) else gcd (Suc x, y - x))"


text {*
  \medskip The silly @{term g} function: example of nested recursion.
  Not handled automatically.  In fact, @{term g} is the zero constant
  function.
 *}

consts g :: "nat => nat"
recdef (permissive) g  less_than
  "g 0 = 0"
  "g (Suc x) = g (g x)"

lemma g_terminates: "g x < Suc x"
  apply (induct x rule: g.induct)
   apply (auto simp add: g.simps)
  done

lemma g_zero: "g x = 0"
  apply (induct x rule: g.induct)
   apply (simp_all add: g.simps g_terminates)
  done


consts Div :: "nat * nat => nat * nat"
recdef Div  "measure fst"
  "Div (0, x) = (0, 0)"
  "Div (Suc x, y) =
    (let (q, r) = Div (x, y)
    in if y \<le> Suc r then (Suc q, 0) else (q, Suc r))"

text {*
  \medskip Not handled automatically.  Should be the predecessor
  function, but there is an unnecessary "looping" recursive call in
  @{term "k 1"}.
*}

consts k :: "nat => nat"
recdef (permissive) k  less_than
  "k 0 = 0"
  "k (Suc n) =
   (let x = k 1
    in if 0 = 1 then k (Suc 1) else n)"

consts part :: "('a => bool) * 'a list * 'a list * 'a list => 'a list * 'a list"
recdef part  "measure (\<lambda>(P, l, l1, l2). size l)"
  "part (P, [], l1, l2) = (l1, l2)"
  "part (P, h # rst, l1, l2) =
    (if P h then part (P, rst, h # l1, l2)
    else part (P, rst, l1, h # l2))"

consts fqsort :: "('a => 'a => bool) * 'a list => 'a list"
recdef (permissive) fqsort  "measure (size o snd)"
  "fqsort (ord, []) = []"
  "fqsort (ord, x # rst) =
  (let (less, more) = part ((\<lambda>y. ord y x), rst, ([], []))
  in fqsort (ord, less) @ [x] @ fqsort (ord, more))"

text {*
  \medskip Silly example which demonstrates the occasional need for
  additional congruence rules (here: @{thm [source] map_cong}).  If
  the congruence rule is removed, an unprovable termination condition
  is generated!  Termination not proved automatically.  TFL requires
  @{term [source] "\<lambda>x. mapf x"} instead of @{term [source] mapf}.
*}

consts mapf :: "nat => nat list"
recdef (permissive) mapf  "measure (\<lambda>m. m)"
  "mapf 0 = []"
  "mapf (Suc n) = concat (map (\<lambda>x. mapf x) (replicate n n))"
  (hints cong: map_cong)

recdef_tc mapf_tc: mapf
  apply (rule allI)
  apply (case_tac "n = 0")
   apply simp_all
  done

text {* Removing the termination condition from the generated thms: *}

lemma "mapf (Suc n) = concat (map mapf (replicate n n))"
  apply (simp add: mapf.simps mapf_tc)
  done

lemmas mapf_induct = mapf.induct [OF mapf_tc]

end
