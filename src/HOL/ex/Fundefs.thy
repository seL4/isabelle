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
thm fib.pinduct

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
by induct auto

termination nz
  apply (auto_term "less_than") -- {* Oops, it left us something to prove *}
  by (auto simp:nz_is_zero)

thm nz.simps
thm nz.induct


section {* More general patterns *}

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
termination by (auto_term "measure (\<lambda>(x,y). x + y)")

thm gcd2.simps
thm gcd2.induct


text {* General patterns allow even strange definitions: *}
consts ev :: "nat \<Rightarrow> bool"
function
  "ev (2 * n) = True"
  "ev (2 * n + 1) = False"
proof -  -- {* completeness is more difficult here \dots *}
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

end
