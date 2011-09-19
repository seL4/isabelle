(*  Title:      HOL/ex/Fundefs.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Examples of function definitions *}

theory Fundefs 
imports Parity "~~/src/HOL/Library/Monad_Syntax"
begin

subsection {* Very basic *}

fun fib :: "nat \<Rightarrow> nat"
where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text {* partial simp and induction rules: *}
thm fib.psimps
thm fib.pinduct

text {* There is also a cases rule to distinguish cases along the definition *}
thm fib.cases


text {* total simp and induction rules: *}
thm fib.simps
thm fib.induct

subsection {* Currying *}

fun add
where
  "add 0 y = y"
| "add (Suc x) y = Suc (add x y)"

thm add.simps
thm add.induct -- {* Note the curried induction predicate *}


subsection {* Nested recursion *}

function nz 
where
  "nz 0 = 0"
| "nz (Suc x) = nz (nz x)"
by pat_completeness auto

lemma nz_is_zero: -- {* A lemma we need to prove termination *}
  assumes trm: "nz_dom x"
  shows "nz x = 0"
using trm
by induct (auto simp: nz.psimps)

termination nz
  by (relation "less_than") (auto simp:nz_is_zero)

thm nz.simps
thm nz.induct

text {* Here comes McCarthy's 91-function *}


function f91 :: "nat => nat"
where
  "f91 n = (if 100 < n then n - 10 else f91 (f91 (n + 11)))"
by pat_completeness auto

(* Prove a lemma before attempting a termination proof *)
lemma f91_estimate: 
  assumes trm: "f91_dom n"
  shows "n < f91 n + 11"
using trm by induct (auto simp: f91.psimps)

termination
proof
  let ?R = "measure (%x. 101 - x)"
  show "wf ?R" ..

  fix n::nat assume "~ 100 < n" (* Inner call *)
  thus "(n + 11, n) : ?R" by simp

  assume inner_trm: "f91_dom (n + 11)" (* Outer call *)
  with f91_estimate have "n + 11 < f91 (n + 11) + 11" .
  with `~ 100 < n` show "(f91 (n + 11), n) : ?R" by simp 
qed

text{* Now trivial (even though it does not belong here): *}
lemma "f91 n = (if 100 < n then n - 10 else 91)"
by (induct n rule:f91.induct) auto


subsection {* More general patterns *}

subsubsection {* Overlapping patterns *}

text {* Currently, patterns must always be compatible with each other, since
no automatic splitting takes place. But the following definition of
gcd is ok, although patterns overlap: *}

fun gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd2 x 0 = x"
| "gcd2 0 y = y"
| "gcd2 (Suc x) (Suc y) = (if x < y then gcd2 (Suc x) (y - x)
                                    else gcd2 (x - y) (Suc y))"

thm gcd2.simps
thm gcd2.induct

subsubsection {* Guards *}

text {* We can reformulate the above example using guarded patterns *}

function gcd3 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd3 x 0 = x"
| "gcd3 0 y = y"
| "x < y \<Longrightarrow> gcd3 (Suc x) (Suc y) = gcd3 (Suc x) (y - x)"
| "\<not> x < y \<Longrightarrow> gcd3 (Suc x) (Suc y) = gcd3 (x - y) (Suc y)"
  apply (case_tac x, case_tac a, auto)
  apply (case_tac ba, auto)
  done
termination by lexicographic_order

thm gcd3.simps
thm gcd3.induct


text {* General patterns allow even strange definitions: *}

function ev :: "nat \<Rightarrow> bool"
where
  "ev (2 * n) = True"
| "ev (2 * n + 1) = False"
proof -  -- {* completeness is more difficult here \dots *}
  fix P :: bool
    and x :: nat
  assume c1: "\<And>n. x = 2 * n \<Longrightarrow> P"
    and c2: "\<And>n. x = 2 * n + 1 \<Longrightarrow> P"
  have divmod: "x = 2 * (x div 2) + (x mod 2)" by auto
  show "P"
  proof cases
    assume "x mod 2 = 0"
    with divmod have "x = 2 * (x div 2)" by simp
    with c1 show "P" .
  next
    assume "x mod 2 \<noteq> 0"
    hence "x mod 2 = 1" by simp
    with divmod have "x = 2 * (x div 2) + 1" by simp
    with c2 show "P" .
  qed
qed presburger+ -- {* solve compatibility with presburger *} 
termination by lexicographic_order

thm ev.simps
thm ev.induct
thm ev.cases


subsection {* Mutual Recursion *}

fun evn od :: "nat \<Rightarrow> bool"
where
  "evn 0 = True"
| "od 0 = False"
| "evn (Suc n) = od n"
| "od (Suc n) = evn n"

thm evn.simps
thm od.simps

thm evn_od.induct
thm evn_od.termination


subsection {* Definitions in local contexts *}

locale my_monoid = 
fixes opr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and un :: "'a"
assumes assoc: "opr (opr x y) z = opr x (opr y z)"
  and lunit: "opr un x = x"
  and runit: "opr x un = x"
begin

fun foldR :: "'a list \<Rightarrow> 'a"
where
  "foldR [] = un"
| "foldR (x#xs) = opr x (foldR xs)"

fun foldL :: "'a list \<Rightarrow> 'a"
where
  "foldL [] = un"
| "foldL [x] = x"
| "foldL (x#y#ys) = foldL (opr x y # ys)" 

thm foldL.simps

lemma foldR_foldL: "foldR xs = foldL xs"
by (induct xs rule: foldL.induct) (auto simp:lunit runit assoc)

thm foldR_foldL

end

thm my_monoid.foldL.simps
thm my_monoid.foldR_foldL


subsection {* Partial Function Definitions *}

text {* Partial functions in the option monad: *}

partial_function (option)
  collatz :: "nat \<Rightarrow> nat list option"
where
  "collatz n =
  (if n \<le> 1 then Some [n]
   else if even n 
     then do { ns \<leftarrow> collatz (n div 2); Some (n # ns) }
     else do { ns \<leftarrow> collatz (3 * n + 1);  Some (n # ns)})"

declare collatz.simps[code]
value "collatz 23"


text {* Tail-recursive functions: *}

partial_function (tailrec) fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "fixpoint f x = (if f x = x then x else fixpoint f (f x))"


subsection {* Regression tests *}

text {* The following examples mainly serve as tests for the 
  function package *}

fun listlen :: "'a list \<Rightarrow> nat"
where
  "listlen [] = 0"
| "listlen (x#xs) = Suc (listlen xs)"

(* Context recursion *)

fun f :: "nat \<Rightarrow> nat" 
where
  zero: "f 0 = 0"
| succ: "f (Suc n) = (if f n = 0 then 0 else f n)"


(* A combination of context and nested recursion *)
function h :: "nat \<Rightarrow> nat"
where
  "h 0 = 0"
| "h (Suc n) = (if h n = 0 then h (h n) else h n)"
  by pat_completeness auto


(* Context, but no recursive call: *)
fun i :: "nat \<Rightarrow> nat"
where
  "i 0 = 0"
| "i (Suc n) = (if n = 0 then 0 else i n)"


(* Tupled nested recursion *)
fun fa :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fa 0 y = 0"
| "fa (Suc n) y = (if fa n y = 0 then 0 else fa n y)"

(* Let *)
fun j :: "nat \<Rightarrow> nat"
where
  "j 0 = 0"
| "j (Suc n) = (let u = n  in Suc (j u))"


(* There were some problems with fresh names\<dots> *)
function  k :: "nat \<Rightarrow> nat"
where
  "k x = (let a = x; b = x in k x)"
  by pat_completeness auto


function f2 :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "f2 p = (let (x,y) = p in f2 (y,x))"
  by pat_completeness auto


(* abbreviations *)
fun f3 :: "'a set \<Rightarrow> bool"
where
  "f3 x = finite x"


(* Simple Higher-Order Recursion *)
datatype 'a tree = 
  Leaf 'a 
  | Branch "'a tree list"

fun treemap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
  "treemap fn (Leaf n) = (Leaf (fn n))"
| "treemap fn (Branch l) = (Branch (map (treemap fn) l))"

fun tinc :: "nat tree \<Rightarrow> nat tree"
where
  "tinc (Leaf n) = Leaf (Suc n)"
| "tinc (Branch l) = Branch (map tinc l)"

fun testcase :: "'a tree \<Rightarrow> 'a list"
where
  "testcase (Leaf a) = [a]"
| "testcase (Branch x) =
    (let xs = concat (map testcase x);
         ys = concat (map testcase x) in
     xs @ ys)"


(* Pattern matching on records *)
record point =
  Xcoord :: int
  Ycoord :: int

function swp :: "point \<Rightarrow> point"
where
  "swp \<lparr> Xcoord = x, Ycoord = y \<rparr> = \<lparr> Xcoord = y, Ycoord = x \<rparr>"
proof -
  fix P x
  assume "\<And>xa y. x = \<lparr>Xcoord = xa, Ycoord = y\<rparr> \<Longrightarrow> P"
  thus "P"
    by (cases x)
qed auto
termination by rule auto


(* The diagonal function *)
fun diag :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat"
where
  "diag x True False = 1"
| "diag False y True = 2"
| "diag True False z = 3"
| "diag True True True = 4"
| "diag False False False = 5"


(* Many equations (quadratic blowup) *)
datatype DT = 
  A | B | C | D | E | F | G | H | I | J | K | L | M | N | P
| Q | R | S | T | U | V

fun big :: "DT \<Rightarrow> nat"
where
  "big A = 0" 
| "big B = 0" 
| "big C = 0" 
| "big D = 0" 
| "big E = 0" 
| "big F = 0" 
| "big G = 0" 
| "big H = 0" 
| "big I = 0" 
| "big J = 0" 
| "big K = 0" 
| "big L = 0" 
| "big M = 0" 
| "big N = 0" 
| "big P = 0" 
| "big Q = 0" 
| "big R = 0" 
| "big S = 0" 
| "big T = 0" 
| "big U = 0" 
| "big V = 0"


(* automatic pattern splitting *)
fun
  f4 :: "nat \<Rightarrow> nat \<Rightarrow> bool" 
where
  "f4 0 0 = True"
| "f4 _ _ = False"


(* polymorphic partial_function *)
partial_function (option) f5 :: "'a list \<Rightarrow> 'a option"
where
  "f5 x = f5 x"

end
