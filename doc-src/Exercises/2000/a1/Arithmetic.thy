(*<*)
theory Arithmetic = Main:;
(*>*)

subsection  {* Arithmetic *}

subsubsection {* Power *};

text {* Define a primitive recursive function $pow~x~n$ that
computes $x^n$ on natural numbers.  *};

consts
  pow :: "nat => nat => nat";

text {*
Prove the well known equation $x^{m \cdot n} = (x^m)^n$:
*};

theorem pow_mult: "pow x (m * n) = pow (pow x m) n";
(*<*)oops(*>*)

text {* Hint: prove a suitable lemma first.  If you need to appeal to
associativity and commutativity of multiplication: the corresponding
simplification rules are named @{text mult_ac}.  *}

subsubsection {* Summation *}

text {*
Define a (primitive recursive) function $sum~ns$ that sums a list
of natural numbers: $sum [n_1, \dots, n_k] = n_1 + \cdots + n_k$.
*}

consts
  sum :: "nat list => nat";

text {*
Show that $sum$ is compatible with $rev$. You may need a lemma.
*}

theorem sum_rev: "sum (rev ns) = sum ns"
(*<*)oops(*>*)

text {*
Define a function $Sum~f~k$ that sums $f$ from $0$
up to $k-1$: $Sum~f~k = f~0 + \cdots + f(k - 1)$.
*};

consts
  Sum :: "(nat => nat) => nat => nat";

text {*
Show the following equations for the pointwise summation of functions.
Determine first what the expression @{text whatever} should be.
*};

theorem "Sum (%i. f i + g i) k = Sum f k + Sum g k";
(*<*)oops(*>*)

theorem "Sum f (k + l) = Sum f k + Sum whatever l";
(*<*)oops(*>*)

text {*
What is the relationship between @{term sum} and @{text Sum}?
Prove the following equation, suitably instantiated.
*};

theorem "Sum f k = sum whatever";
(*<*)oops(*>*)

text {*
Hint: familiarize yourself with the predefined functions @{term map} and
@{term"[i..j(]"} on lists in theory List.
*}

(*<*)
end
(*>*)