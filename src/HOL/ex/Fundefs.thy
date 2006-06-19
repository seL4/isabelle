(*  Title:      HOL/ex/Fundefs.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

Examples of function definitions using the new "function" package.
*)

theory Fundefs 
imports Main
begin

section {* Very basic *}

consts fib :: "nat \<Rightarrow> nat"
function
  "fib 0 = 1"
  "fib (Suc 0) = 1"
  "fib (Suc (Suc n)) = fib n + fib (Suc n)"
by pat_completeness  -- {* shows that the patterns are complete *}
  auto  -- {* shows that the patterns are compatible *}

text {* we get partial simp and induction rules: *}
thm fib.psimps
thm pinduct

text {* There is also a cases rule to distinguish cases along the definition *}
thm fib.cases

text {* Now termination: *}
termination fib
  by (auto_term "less_than")

thm fib.simps
thm fib.induct


section {* Currying *}

consts add :: "nat \<Rightarrow> nat \<Rightarrow> nat"
function
  "add 0 y = y"
  "add (Suc x) y = Suc (add x y)"
thm add_rel.cases

by pat_completeness auto
termination
  by (auto_term "measure fst")

thm add.induct -- {* Note the curried induction predicate *}


section {* Nested recursion *}

consts nz :: "nat \<Rightarrow> nat"
function
  "nz 0 = 0"
  "nz (Suc x) = nz (nz x)"
by pat_completeness auto

lemma nz_is_zero: -- {* A lemma we need to prove termination *}
  assumes trm: "x \<in> nz_dom"
  shows "nz x = 0"
using trm
apply induct 
apply auto
done

termination nz
  apply (auto_term "less_than") -- {* Oops, it left us something to prove *}
  by (auto simp:nz_is_zero)

thm nz.simps
thm nz.induct

text {* Here comes McCarthy's 91-function *}

consts f91 :: "nat => nat"
function 
  "f91 n = (if 100 < n then n - 10 else f91 (f91 (n + 11)))"
by pat_completeness auto

(* Prove a lemma before attempting a termination proof *)
lemma f91_estimate: 
  assumes trm: "n : f91_dom" 
  shows "n < f91 n + 11"
using trm by induct auto

(* Now go for termination *)
termination
proof
  let ?R = "measure (%x. 101 - x)"
  show "wf ?R" ..

  fix n::nat assume "~ 100 < n" (* Inner call *)
  thus "(n + 11, n) : ?R"
    by simp arith

  assume inner_trm: "n + 11 : f91_dom" (* Outer call *)
  with f91_estimate have "n + 11 < f91 (n + 11) + 11" .
  with `~ 100 < n` show "(f91 (n + 11), n) : ?R"
    by simp arith
qed



section {* More general patterns *}

subsection {* Overlapping patterns *}

text {* Currently, patterns must always be compatible with each other, since
no automatich splitting takes place. But the following definition of
gcd is ok, although patterns overlap: *}

consts gcd2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
function
  "gcd2 x 0 = x"
  "gcd2 0 y = y"
  "gcd2 (Suc x) (Suc y) = (if x < y then gcd2 (Suc x) (y - x)
                                else gcd2 (x - y) (Suc y))"
by pat_completeness auto
termination 
  by (auto_term "measure (\<lambda>(x,y). x + y)")

thm gcd2.simps
thm gcd2.induct


subsection {* Guards *}

text {* We can reformulate the above example using guarded patterns *}

consts gcd3 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
function
  "gcd3 x 0 = x"
  "gcd3 0 y = y"
  "x < y \<Longrightarrow> gcd3 (Suc x) (Suc y) = gcd3 (Suc x) (y - x)"
  "\<not> x < y \<Longrightarrow> gcd3 (Suc x) (Suc y) = gcd3 (x - y) (Suc y)"
  apply (case_tac x, case_tac a, auto)
  apply (case_tac ba, auto)
  done
termination 
  by (auto_term "measure (\<lambda>(x,y). x + y)")

thm gcd3.simps
thm gcd3.induct



text {* General patterns allow even strange definitions: *}
consts ev :: "nat \<Rightarrow> bool"
function
  "ev (2 * n) = True"
  "ev (2 * n + 1) = False"
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
qed presburger+   -- {* solve compatibility with presburger *}
termination by (auto_term "{}")

thm ev.simps
thm ev.induct
thm ev.cases


section {* Mutual Recursion *}


consts
  evn :: "nat \<Rightarrow> bool"
  od :: "nat \<Rightarrow> bool"

function
  "evn 0 = True"
  "evn (Suc n) = od n"
and
  "od 0 = False"
  "od (Suc n) = evn n"
  by pat_completeness auto

thm evn.psimps
thm od.psimps

thm evn_od.pinduct
thm evn_od.termination
thm evn_od.domintros

termination
  by (auto_term "measure (sum_case (%n. n) (%n. n))")

thm evn.simps
thm od.simps


end
