(*  Title:      HOL/ex/Functions.thy
    Author:     Alexander Krauss, TU Muenchen
*)

section \<open>Examples of function definitions\<close>

theory Functions
imports Main "HOL-Library.Monad_Syntax"
begin

subsection \<open>Very basic\<close>

fun fib :: "nat \<Rightarrow> nat"
where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text \<open>Partial simp and induction rules:\<close>
thm fib.psimps
thm fib.pinduct

text \<open>There is also a cases rule to distinguish cases along the definition:\<close>
thm fib.cases


text \<open>Total simp and induction rules:\<close>
thm fib.simps
thm fib.induct

text \<open>Elimination rules:\<close>
thm fib.elims


subsection \<open>Currying\<close>

fun add
where
  "add 0 y = y"
| "add (Suc x) y = Suc (add x y)"

thm add.simps
thm add.induct  \<comment> \<open>Note the curried induction predicate\<close>


subsection \<open>Nested recursion\<close>

function nz
where
  "nz 0 = 0"
| "nz (Suc x) = nz (nz x)"
by pat_completeness auto

lemma nz_is_zero:  \<comment> \<open>A lemma we need to prove termination\<close>
  assumes trm: "nz_dom x"
  shows "nz x = 0"
using trm
by induct (auto simp: nz.psimps)

termination nz
  by (relation "less_than") (auto simp:nz_is_zero)

thm nz.simps
thm nz.induct


subsubsection \<open>Here comes McCarthy's 91-function\<close>

function f91 :: "nat \<Rightarrow> nat"
where
  "f91 n = (if 100 < n then n - 10 else f91 (f91 (n + 11)))"
by pat_completeness auto

text \<open>Prove a lemma before attempting a termination proof:\<close>
lemma f91_estimate:
  assumes trm: "f91_dom n"
  shows "n < f91 n + 11"
using trm by induct (auto simp: f91.psimps)

termination
proof
  let ?R = "measure (\<lambda>x. 101 - x)"
  show "wf ?R" ..

  fix n :: nat
  assume "\<not> 100 < n"  \<comment> \<open>Inner call\<close>
  then show "(n + 11, n) \<in> ?R" by simp

  assume inner_trm: "f91_dom (n + 11)"  \<comment> \<open>Outer call\<close>
  with f91_estimate have "n + 11 < f91 (n + 11) + 11" .
  with \<open>\<not> 100 < n\<close> show "(f91 (n + 11), n) \<in> ?R" by simp
qed

text \<open>Now trivial (even though it does not belong here):\<close>
lemma "f91 n = (if 100 < n then n - 10 else 91)"
  by (induct n rule: f91.induct) auto


subsubsection \<open>Here comes Takeuchi's function\<close>

definition tak_m1 where "tak_m1 = (\<lambda>(x,y,z). if x \<le> y then 0 else 1)"
definition tak_m2 where "tak_m2 = (\<lambda>(x,y,z). nat (Max {x, y, z} - Min {x, y, z}))"
definition tak_m3 where "tak_m3 = (\<lambda>(x,y,z). nat (x - Min {x, y, z}))"

function tak :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "tak x y z = (if x \<le> y then y else tak (tak (x-1) y z) (tak (y-1) z x) (tak (z-1) x y))"
  by auto

lemma tak_pcorrect:
  "tak_dom (x, y, z) \<Longrightarrow> tak x y z = (if x \<le> y then y else if y \<le> z then z else x)"
  by (induction x y z rule: tak.pinduct) (auto simp: tak.psimps)

termination
  by (relation "tak_m1 <*mlex*> tak_m2 <*mlex*> tak_m3 <*mlex*> {}")
     (auto simp: mlex_iff wf_mlex tak_pcorrect tak_m1_def tak_m2_def tak_m3_def min_def max_def)

theorem tak_correct: "tak x y z = (if x \<le> y then y else if y \<le> z then z else x)"
  by (induction x y z rule: tak.induct) auto


subsection \<open>More general patterns\<close>

subsubsection \<open>Overlapping patterns\<close>

text \<open>
  Currently, patterns must always be compatible with each other, since
  no automatic splitting takes place. But the following definition of
  GCD is OK, although patterns overlap:
\<close>

fun gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd2 x 0 = x"
| "gcd2 0 y = y"
| "gcd2 (Suc x) (Suc y) = (if x < y then gcd2 (Suc x) (y - x)
                                    else gcd2 (x - y) (Suc y))"

thm gcd2.simps
thm gcd2.induct


subsubsection \<open>Guards\<close>

text \<open>We can reformulate the above example using guarded patterns:\<close>

function gcd3 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd3 x 0 = x"
| "gcd3 0 y = y"
| "gcd3 (Suc x) (Suc y) = gcd3 (Suc x) (y - x)" if "x < y"
| "gcd3 (Suc x) (Suc y) = gcd3 (x - y) (Suc y)" if "\<not> x < y"
  apply (case_tac x, case_tac a, auto)
  apply (case_tac ba, auto)
  done
termination by lexicographic_order

thm gcd3.simps
thm gcd3.induct


text \<open>General patterns allow even strange definitions:\<close>

function ev :: "nat \<Rightarrow> bool"
where
  "ev (2 * n) = True"
| "ev (2 * n + 1) = False"
proof -  \<comment> \<open>completeness is more difficult here \dots\<close>
  fix P :: bool
  fix x :: nat
  assume c1: "\<And>n. x = 2 * n \<Longrightarrow> P"
    and c2: "\<And>n. x = 2 * n + 1 \<Longrightarrow> P"
  have divmod: "x = 2 * (x div 2) + (x mod 2)" by auto
  show P
  proof (cases "x mod 2 = 0")
    case True
    with divmod have "x = 2 * (x div 2)" by simp
    with c1 show "P" .
  next
    case False
    then have "x mod 2 = 1" by simp
    with divmod have "x = 2 * (x div 2) + 1" by simp
    with c2 show "P" .
  qed
qed presburger+  \<comment> \<open>solve compatibility with presburger\<close>
termination by lexicographic_order

thm ev.simps
thm ev.induct
thm ev.cases


subsection \<open>Mutual Recursion\<close>

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

thm evn.elims
thm od.elims


subsection \<open>Definitions in local contexts\<close>

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
| "foldR (x # xs) = opr x (foldR xs)"

fun foldL :: "'a list \<Rightarrow> 'a"
where
  "foldL [] = un"
| "foldL [x] = x"
| "foldL (x # y # ys) = foldL (opr x y # ys)"

thm foldL.simps

lemma foldR_foldL: "foldR xs = foldL xs"
  by (induct xs rule: foldL.induct) (auto simp:lunit runit assoc)

thm foldR_foldL

end

thm my_monoid.foldL.simps
thm my_monoid.foldR_foldL


subsection \<open>\<open>fun_cases\<close>\<close>

subsubsection \<open>Predecessor\<close>

fun pred :: "nat \<Rightarrow> nat"
where
  "pred 0 = 0"
| "pred (Suc n) = n"

thm pred.elims

lemma
  assumes "pred x = y"
  obtains "x = 0" "y = 0" | "n" where "x = Suc n" "y = n"
  by (fact pred.elims[OF assms])


text \<open>If the predecessor of a number is 0, that number must be 0 or 1.\<close>

fun_cases pred0E[elim]: "pred n = 0"

lemma "pred n = 0 \<Longrightarrow> n = 0 \<or> n = Suc 0"
  by (erule pred0E) metis+

text \<open>
  Other expressions on the right-hand side also work, but whether the
  generated rule is useful depends on how well the simplifier can
  simplify it. This example works well:
\<close>

fun_cases pred42E[elim]: "pred n = 42"

lemma "pred n = 42 \<Longrightarrow> n = 43"
  by (erule pred42E)


subsubsection \<open>List to option\<close>

fun list_to_option :: "'a list \<Rightarrow> 'a option"
where
  "list_to_option [x] = Some x"
| "list_to_option _ = None"

fun_cases list_to_option_NoneE: "list_to_option xs = None"
  and list_to_option_SomeE: "list_to_option xs = Some x"

lemma "list_to_option xs = Some y \<Longrightarrow> xs = [y]"
  by (erule list_to_option_SomeE)


subsubsection \<open>Boolean Functions\<close>

fun xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "xor False False = False"
| "xor True True = False"
| "xor _ _ = True"

thm xor.elims

text \<open>
  \<open>fun_cases\<close> does not only recognise function equations, but also works with
  functions that return a boolean, e.g.:
\<close>

fun_cases xor_TrueE: "xor a b" and xor_FalseE: "\<not>xor a b"
print_theorems


subsubsection \<open>Many parameters\<close>

fun sum4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sum4 a b c d = a + b + c + d"

fun_cases sum40E: "sum4 a b c d = 0"

lemma "sum4 a b c d = 0 \<Longrightarrow> a = 0"
  by (erule sum40E)


subsection \<open>Partial Function Definitions\<close>

text \<open>Partial functions in the option monad:\<close>

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


text \<open>Tail-recursive functions:\<close>

partial_function (tailrec) fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "fixpoint f x = (if f x = x then x else fixpoint f (f x))"


subsection \<open>Regression tests\<close>

text \<open>
  The following examples mainly serve as tests for the
  function package.
\<close>

fun listlen :: "'a list \<Rightarrow> nat"
where
  "listlen [] = 0"
| "listlen (x#xs) = Suc (listlen xs)"


subsubsection \<open>Context recursion\<close>

fun f :: "nat \<Rightarrow> nat"
where
  zero: "f 0 = 0"
| succ: "f (Suc n) = (if f n = 0 then 0 else f n)"


subsubsection \<open>A combination of context and nested recursion\<close>

function h :: "nat \<Rightarrow> nat"
where
  "h 0 = 0"
| "h (Suc n) = (if h n = 0 then h (h n) else h n)"
by pat_completeness auto


subsubsection \<open>Context, but no recursive call\<close>

fun i :: "nat \<Rightarrow> nat"
where
  "i 0 = 0"
| "i (Suc n) = (if n = 0 then 0 else i n)"


subsubsection \<open>Tupled nested recursion\<close>

fun fa :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fa 0 y = 0"
| "fa (Suc n) y = (if fa n y = 0 then 0 else fa n y)"


subsubsection \<open>Let\<close>

fun j :: "nat \<Rightarrow> nat"
where
  "j 0 = 0"
| "j (Suc n) = (let u = n in Suc (j u))"


text \<open>There were some problems with fresh names \dots\<close>
function  k :: "nat \<Rightarrow> nat"
where
  "k x = (let a = x; b = x in k x)"
  by pat_completeness auto


function f2 :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
where
  "f2 p = (let (x,y) = p in f2 (y,x))"
  by pat_completeness auto


subsubsection \<open>Abbreviations\<close>

fun f3 :: "'a set \<Rightarrow> bool"
where
  "f3 x = finite x"


subsubsection \<open>Simple Higher-Order Recursion\<close>

datatype 'a tree = Leaf 'a | Branch "'a tree list"

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


subsubsection \<open>Pattern matching on records\<close>

record point =
  Xcoord :: int
  Ycoord :: int

function swp :: "point \<Rightarrow> point"
where
  "swp \<lparr> Xcoord = x, Ycoord = y \<rparr> = \<lparr> Xcoord = y, Ycoord = x \<rparr>"
proof -
  fix P x
  assume "\<And>xa y. x = \<lparr>Xcoord = xa, Ycoord = y\<rparr> \<Longrightarrow> P"
  then show P by (cases x)
qed auto
termination by rule auto


subsubsection \<open>The diagonal function\<close>

fun diag :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat"
where
  "diag x True False = 1"
| "diag False y True = 2"
| "diag True False z = 3"
| "diag True True True = 4"
| "diag False False False = 5"


subsubsection \<open>Many equations (quadratic blowup)\<close>

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


subsubsection \<open>Automatic pattern splitting\<close>

fun f4 :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "f4 0 0 = True"
| "f4 _ _ = False"


subsubsection \<open>Polymorphic partial-function\<close>

partial_function (option) f5 :: "'a list \<Rightarrow> 'a option"
where
  "f5 x = f5 x"

end
