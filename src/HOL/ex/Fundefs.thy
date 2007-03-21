(*  Title:      HOL/ex/Fundefs.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

Examples of function definitions using the new "function" package.
*)

theory Fundefs 
imports Main
begin

section {* Very basic *}

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

section {* Currying *}

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "add 0 y = y"
| "add (Suc x) y = Suc (add x y)"

thm add.simps
thm add.induct -- {* Note the curried induction predicate *}


section {* Nested recursion *}

function nz :: "nat \<Rightarrow> nat"
where
  "nz 0 = 0"
| "nz (Suc x) = nz (nz x)"
by pat_completeness auto

lemma nz_is_zero: -- {* A lemma we need to prove termination *}
  assumes trm: "nz_dom x"
  shows "nz x = 0"
using trm
by induct auto

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
using trm by induct auto

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



section {* More general patterns *}

subsection {* Overlapping patterns *}

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

subsection {* Guards *}

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


section {* Mutual Recursion *}

fun evn od :: "nat \<Rightarrow> bool"
where
  "evn 0 = True"
| "od 0 = False"
| "evn (Suc n) = od n"
| "od (Suc n) = evn n"

thm evn.simps
thm od.simps

thm evn_od.pinduct
thm evn_od.termination




end
