
(*<*) theory a5 = Main: (*>*)

subsection {* The Euclidean Algorithm -- Inductively *}

subsubsection {* Rules without Base Case *}

text {* Show that the following
*}

consts evenempty :: "nat set"
inductive evenempty
  intros
  Add2Ie: "n \<in> evenempty \<Longrightarrow> Suc(Suc n) \<in> evenempty"

text {* defines the empty set: *}

lemma evenempty_empty: "evenempty = {}"
(*<*) oops (*>*)


subsubsection {* The Euclidean Algorithm *}

text {* Define inductively the set @{text gcd}, which characterizes
the greatest common divisor of two natural numbers: *}

(*<*)consts(*>*)
  gcd :: "(nat \<times> nat \<times> nat) set"

text {* Here, @{text "(a,b,g) \<in> gcd"} means that @{text g} is the gcd
of @{text a} und @{text b}. The definition should closely follow the
Euclidean algorithm.

Reminder: The Euclidean algorithm repeatedly subtracts the smaller
from the larger number, until one of the numbers is 0. Then, the other
number is the gcd. *}

text {* Now, compute the gcd of 15 and 10: *}
lemma "(15, 10, ?g)  \<in> gcd"
(*<*) oops (*>*)

text {* How does your algorithm behave on special cases as the following?  *}
lemma "(0, 0, ?g)  \<in> gcd"
(*<*) oops (*>*)

text {* Show that the gcd is really a divisor (for the proof, you need an appropriate lemma): *}

lemma gcd_divides: "(a,b,g) \<in> gcd \<Longrightarrow> g dvd a \<and> g dvd b"
(*<*) oops (*>*)

text {* Show that the gcd is the greatest common divisor: *}

lemma gcd_greatest [rule_format]: "(a,b,g) \<in> gcd \<Longrightarrow>
  0 < a \<or> 0 < b \<longrightarrow> (\<forall> d. d dvd a \<longrightarrow> d dvd b \<longrightarrow> d \<le> g)"
(*<*) oops (*>*)

text {* Here as well, you will have to prove a suitable lemma. What is
the precondition @{text "0 < a \<or> 0 < b"} good for?

So far, we have only shown that @{text gcd} is correct, but your
algorithm might not compute a result for all values @{text
"a,b"}. Thus, show completeness of the algorithm: *}

lemma gcd_defined: "\<forall> a b. \<exists> g. (a, b, g) \<in> gcd"
(*<*) oops (*>*)

text {* The following lemma, proved by course-of-value recursion over
@{text n}, may be useful. Why does standard induction over natural
numbers not work here?  *}

lemma gcd_defined_aux [rule_format]: 
  "\<forall> a b. (a + b) \<le> n \<longrightarrow> (\<exists> g. (a, b, g) \<in> gcd)"
apply (induct rule: nat_less_induct)
apply clarify

(*<*) oops (*>*)

text {* The idea is to show that @{text gcd} yields a result for all
@{text "a, b"} whenever it is known that @{text gcd} yields a result
for all @{text "a', b'"} whose sum is smaller than @{text "a + b"}.

In order to prove this lemma, make case distinctions corresponding to
the different clauses of the algorithm, and show how to reduce
computation of @{text gcd} for @{text "a, b"} to computation of @{text
gcd} for suitable smaller @{text "a', b'"}.

*}


(*<*) end (*>*)

