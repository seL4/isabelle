
(*<*) theory a4 = Main: (*>*)

subsection {* Natural Deduction -- Predicate Logic; Sets as Lists *}


subsubsection {* Predicate Logic Formulae *}

text {*

We are again talking about proofs in the calculus of Natural
Deduction. In addition to the rules of section~\ref{psv0304a3}, you may now also use


  @{text "exI:"}~@{thm exI[no_vars]}\\
  @{text "exE:"}~@{thm exE[no_vars]}\\
  @{text "allI:"}~@{thm allI[no_vars]}\\
  @{text "allE:"}~@{thm allE[no_vars]}\\

Give a proof of the following propositions or an argument why the formula is not valid:
*}


lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
(*<*) oops (*>*)

lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
(*<*) oops (*>*)

lemma "((\<forall> x. P x)  \<and> (\<forall> x. Q x)) = (\<forall> x. (P x \<and> Q x))"
(*<*) oops (*>*)

lemma "((\<forall> x. P x) \<or> (\<forall> x. Q x)) = (\<forall> x. (P x \<or> Q x))"
(*<*) oops (*>*)

lemma "((\<exists> x. P x) \<or> (\<exists> x. Q x)) = (\<exists> x. (P x \<or> Q x))"
(*<*) oops (*>*)

lemma "\<exists>x. (P x \<longrightarrow> (\<forall>x. P x))"
(*<*) oops (*>*)


subsubsection {* Sets as Lists *}

text {* Finite sets can obviously be implemented by lists. In the
following, you will be asked to implement the set operations union,
intersection and difference and to show that these implementations are
correct. Thus, for a function  *}

(*<*) consts (*>*)
  list_union :: "['a list, 'a list] \<Rightarrow> 'a list"

text {* to be defined by you it has to be shown that *}

lemma "set (list_union xs ys) = set xs \<union> set ys"
(*<*) oops (*>*)


text {* In addition, the functions should be space efficient in the
sense that one obtains lists without duplicates (@{text "distinct"})
whenever the parameters of the functions are duplicate-free. Thus, for
example, *}


lemma [rule_format]: 
  "distinct xs \<longrightarrow> distinct ys \<longrightarrow> (distinct (list_union xs ys))"
(*<*) oops (*>*)

text {* \emph{Hint:} @{text "distinct"} is defined in @{text
List.thy}. Also the function @{text mem} and the lemma @{text
set_mem_eq} may be useful. *}


subsubsection {* Quantification over Sets *}

text {* Define a set @{text S} such that the following proposition holds: *}

lemma "((\<forall> x \<in> A. P x) \<and> (\<forall> x \<in> B. P x)) \<longrightarrow> (\<forall> x \<in> S. P x)"
(*<*) oops (*>*)


text {* Define a predicate @{text P} such that *}

lemma "\<forall> x \<in> A. P (f x) \<Longrightarrow>  \<forall> y \<in> f ` A. Q y"
(*<*) oops (*>*)



(*<*) end (*>*)

