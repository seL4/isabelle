(*  Title:      HOL/Imperative_HOL/ex/Congproc_Ex.thy
    Author:     Norbert Schirmer, Apple, 2024
*)

section \<open>Examples for congruence procedures (congprocs)\<close>

theory Congproc_Ex
  imports "../Imperative_HOL"
begin

text \<open>The simplifier works bottom up, which means that when invoked on a (compound) term it first
descends into the subterms to normalise those and then works its way up to the head of the term
trying to apply rewrite rules for the current redex (reducible expression) it encounters on the
way up. Descending into the term can be influenced by congruence rules. Before descending into the
subterms the simplifier checks for a congruence rule for the head of the term. If it finds one
it behaves according to that rule, otherwise the simplifier descends into each subterm subsequently.

While rewrite rules can be complemented with simplification procedures (simprocs) to get even
more programmatic control, congruence rules can be complemented with congruence
procedures (congprocs):

\<^item> Congprocs share the same ML signature as simprocs and provide a similar interface in
  Isabelle/ML as well as Isabelle/Isar:
  @{ML_type "morphism -> Proof.context -> thm option"}
\<^item> Congprocs are triggered by associated term patterns (just like simprocs) not just the head constant
  (which is the case for congruence rules). Like simprocs, congprocs are managed in a term net.
\<^item> Congprocs have precedence over congruence rules (unlike simprocs)
\<^item> In case the term net selects multiple candidates,
  the one with the more specific term pattern is tried first. A pattern
  \<open>p1\<close> is considered more specific than \<open>p2\<close> if \<open>p2\<close> matches \<open>p1\<close> but not vice versa.
\<^item> To avoid surprises the theorems returned by a congproc should follow the structure of
  ordinary congruence rule. Either the conclusion should return an equation where the head of the
  left hand side and right hand side coincide, or the right hand side is already in normal form.
  Otherwise, simplification might skip some relevant subterms or do repeated simplification of
  some subterms. Some fine points are illustrated by the following examples.
\<close>


subsection \<open>Congproc examples with if-then-else\<close>

ML \<open>
fun assert expected eq = if (expected aconvc (Thm.rhs_of eq)) then eq else
  raise error ("unexpected: " ^ @{make_string} eq)

fun assert_equiv expected eq =
  if Pattern.equiv @{theory} (Thm.term_of expected, Thm.term_of (Thm.rhs_of eq)) then eq else
  raise error ("unexpected: " ^ @{make_string} eq)

\<close>
text \<open>The standard setup uses @{thm if_weak_cong}. Only if the condition simplifies to
 \<^term>\<open>True\<close> or \<^term>\<open>False\<close> the branches are simplified.\<close>
experiment fixes a::nat
begin
ML_val \<open>
@{cterm "if a < 2 then a < 2 else \<not> a < 2"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "if a < 2 then a < 2 else \<not> a < 2"}
\<close>
end

text \<open>A congproc that supplies the 'strong' rule @{thm if_cong}\<close>
simproc_setup passive congproc if_cong (\<open>if x then a else b\<close>) = \<open>
  (K (K (K (SOME @{thm if_cong [cong_format]}))))
\<close>

experiment
begin
text \<open>The congproc takes precedence over the cong rules\<close>
declare [[simproc add: if_cong, simp_trace = false]]
ML_val \<open>
@{cterm "if ((a::nat) < 2) then a < 2 else \<not> ((a::nat) < 2)"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm True}
\<close>
end

text \<open>When we replace the congruence rule with a congproc that provides the same
rule we would expect that the result is the same.\<close>

simproc_setup passive congproc if_weak_cong_bad (\<open>if x then a else b\<close>) = \<open>
  (K (K (K (SOME @{thm if_weak_cong [cong_format]}))))
\<close>

experiment
begin

ML_val \<open>
@{cterm "if True then (1::nat) + 2 else 2 + 3"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "Suc (Suc (Suc 0))"}
\<close>


declare if_weak_cong [cong del]
declare [[simproc add: if_weak_cong_bad, simp_trace]]

ML_val \<open>
@{cterm "if True then (1::nat) + 2 else 2 + 3"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "(1::nat) + 2"}
\<close>
text \<open>We do not get the same result. The then-branch is selected but not simplified.
As the simplifier works bottom up it can usually assume that the subterms are already in
'simp normal form'. So the simplifier avoids to revisit the then-branch when it applies
@{thm if_True}. However, the weak congruence rule
@{thm if_weak_cong} only simplifies the condition and neither branch.
As the simplifier analyses congruence rules this rule is classified as weak. Whenever a
redex is simplified (for which a weak congruence rule is active) the simplifier deviates from its
 default behaviour and rewrites the result. However, the simplifier does not analyse the
congproc. To achieve the same result we can explicitly specify it as \<^emph>\<open>weak\<close>.\<close>
end

simproc_setup passive weak_congproc if_weak_cong (\<open>if x then a else b\<close>) = \<open>
  (K (K (K (SOME @{thm if_weak_cong [cong_format]}))))
\<close>

experiment
begin
declare if_weak_cong [cong del]
declare [[simproc add: if_weak_cong, simp_trace]]
ML_val \<open>
@{cterm "if True then (1::nat) + 2 else 2 + 3"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "Suc (Suc (Suc 0))"}
\<close>
end

text \<open>Now some more ambitious congproc that combines the effect of @{thm if_weak_cong} and @{thm if_cong}.
It first simplifies the condition and depending on the result decides to either simplify only
one of the branches (in case the condition evaluates to \<^term>\<open>True\<close> or \<^term>\<open>False\<close>, or otherwise
it simplifies both branches.
\<close>

lemma if_True_weak_cong:
  "P = True \<Longrightarrow> x = x' \<Longrightarrow> (if P then x else y) = (if True then x' else y)"
  by simp

lemma if_False_weak_cong:
  "P = False \<Longrightarrow> y = y' \<Longrightarrow> (if P then x else y) = (if False then x else y')"
  by simp

text \<open>Note that we do not specify the congproc as \<^emph>\<open>weak\<close> as every relevant subterm is
simplified.\<close>
simproc_setup passive congproc if_cong_canonical (\<open>if x then a else b\<close>) = \<open>
  let
    val if_True_weak_cong = @{thm if_True_weak_cong [cong_format]}
    val if_False_weak_cong = @{thm if_False_weak_cong [cong_format]}
    val if_cong = @{thm if_cong [cong_format]}
  in
    (K (fn ctxt => fn ct =>
      let
         val (_, [P, x, y]) = Drule.strip_comb ct
         val P_eq = Simplifier.asm_full_rewrite ctxt P
         val rhs = Thm.dest_equals_rhs (Thm.cprop_of P_eq)
         val rule = (case Thm.term_of rhs of
                       @{term True}  => if_True_weak_cong
                     | @{term False} => if_False_weak_cong
                     | _ => if_cong)
      in
        SOME (rule OF [P_eq])
      end))
   end
\<close>

experiment
begin
declare if_weak_cong [cong del]
declare [[simproc add: if_cong_canonical, simp_trace]]
ML_val \<open>
@{cterm "if True then (1::nat) + 2 else 2 + 3"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "Suc (Suc (Suc 0))"}
\<close>
end

experiment
begin
declare if_weak_cong [cong del]
declare [[simproc add: if_cong_canonical, simp_trace]]
text \<open>Canonical congruence behaviour:
\<^enum> First condition is simplified to True
\<^enum> Congruence rule is selected and then "then-branch" is simplified but "else-branch" is left untouched
\<^enum> Congruence step is finished and now rewriting with @{thm if_True} is done.
Note that there is no attempt to revisit the result, as congproc is not weak.\<close>
ML_val \<open>
@{cterm "if ((2::nat) < 3) then 22 + 2 else 21 + 1"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "24"}
\<close>
end

experiment fixes a ::nat
begin
text \<open>The weak congruence rule shows no effect.\<close>
ML_val \<open>
@{cterm "if a < b then a < b \<longrightarrow> True else \<not> a < b \<longrightarrow> True"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "if a < b then a < b \<longrightarrow> True else \<not> a < b \<longrightarrow> True"}
\<close>

text \<open>The congproc simplifies the term.\<close>
declare if_weak_cong [cong del]
declare [[simproc add: if_cong_canonical, simp_trace]]
ML_val \<open>
@{cterm "if a < b then a < b \<longrightarrow> True else \<not> a < b \<longrightarrow> True"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "True"}
\<close>
end

text \<open>Beware of congprocs that implement non-standard congruence rules, like:\<close>

lemma if_True_cong: "P = True \<Longrightarrow> (if P then x else y) = x"
  by simp

lemma if_False_cong: "P = False \<Longrightarrow> (if P then x else y) = y"
  by simp

simproc_setup passive congproc if_cong_bad (\<open>if x then a else b\<close>) = \<open>
  let
    val if_True_cong = @{thm if_True_cong [cong_format]}
    val if_False_cong = @{thm if_False_cong [cong_format]}
    val if_cong = @{thm if_cong [cong_format]}
  in
    (K (fn ctxt => fn ct =>
      let
         val (_, [P, x, y]) = Drule.strip_comb ct
         val P_eq = Simplifier.asm_full_rewrite ctxt P
         val rhs = Thm.dest_equals_rhs (Thm.cprop_of P_eq)
         val rule = (case Thm.term_of rhs of
                       @{term True}  => if_True_cong
                     | @{term False} => if_False_cong
                     | _ => if_cong )
      in
        SOME (rule OF [P_eq])
      end))
   end
\<close>

experiment
begin
declare if_weak_cong [cong del]
declare [[simproc add: if_cong_bad, simp_trace]]

ML_val \<open>
@{cterm "if ((2::nat) < 3) then 22 + 2 else 21 + 1"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "24"}
\<close>
text \<open>The result is the same as with the canonical congproc. But when inspecting the \<open>simp_trace\<close>
we can  observe some odd congruence behaviour:
\<^enum> First condition is simplified to True
\<^enum> Non-standard congruence rule @{thm if_True_cong} is selected which does
  not have the same head on the right hand side and simply gives back the "then-branch"
\<^enum> Incidently simplification continues on the then-branch as there are simplification rules for
  the redex @{term "22 + 2"}. So we were lucky.

The following example with a nested if-then-else illustrates what can go wrong.
\<close>

ML_val \<open>
@{cterm "if ((2::nat) < 3) then (if ((3::nat) < 2) then 20 + 1 else 20 + 2) else 20 + 3"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "if (3::nat) < 2 then 20 + 1 else 20 + 2"}
\<close>

text \<open>For the a nested if-then-else we get stuck as there is no simplification rule
triggering for the inner if-then-else once it is at the toplevel. Note that it does not
help to specify the congproc as \<^emph>\<open>weak\<close>. The last step of the simplifier was the application
of the congruence rule. No rewrite rule is triggered for the resulting redex so the simplifier
does not revisit the term. Note that congruence rules (and congprocs) are applied only when the
simplifier walks down the term (top-down), simplification rules (and simprocs) on the other hand
are only applied when the simplifier walks up the term (bottom-up). As the simplifier is on its
way up there is no reason to try a congruence rule on the resulting redex.
It only tries to apply simplification rules.

So congprocs should better behave canonically like ordinary congruence rules and
 preserve the head of the redex:
\<close>
end

experiment
begin
declare if_weak_cong [cong del]
declare [[simproc add: if_cong, simp_trace]]

ML_val \<open>
@{cterm "if ((2::nat) < 3) then (if ((3::nat) < 2) then 20 + 1 else 20 + 2) else 20 + 3"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "22"}
\<close>
end

text \<open>Alternatively one can supply a non standard rule if the congproc takes care of the normalisation
of the relevant subterms itself.\<close>

lemma if_True_diy_cong: "P = True \<Longrightarrow> x = x' \<Longrightarrow> (if P then x else y) = x'"
  by simp

lemma if_False_diy_cong: "P = False \<Longrightarrow> y = y' \<Longrightarrow> (if P then x else y) = y'"
  by simp

simproc_setup passive congproc if_cong_diy (\<open>if x then a else b\<close>) = \<open>
  let
    val if_True_diy_cong = @{thm if_True_diy_cong [cong_format]}
    val if_False_diy_cong = @{thm if_False_diy_cong [cong_format]}
    val if_cong = @{thm if_cong [cong_format]}
  in
    (K (fn ctxt => fn ct =>
      let
         val (_, [P, x, y]) = Drule.strip_comb ct
         val P_eq = Simplifier.asm_full_rewrite ctxt P
         val rhs = Thm.dest_equals_rhs (Thm.cprop_of P_eq)
         val (rule, ts)  = (case Thm.term_of rhs of
                       @{term True}  => (if_True_diy_cong, [x])
                     | @{term False} => (if_False_diy_cong, [y])
                     | _ => (if_cong, []) )
         val eqs = map (Simplifier.asm_full_rewrite ctxt) ts \<comment> \<open>explicitly simplify the subterms\<close>
      in
        SOME (rule OF (P_eq::eqs))
      end))
   end
\<close>

experiment
begin
declare if_weak_cong [cong del]
declare [[simproc add: if_cong_diy, simp_trace]]

ML_val \<open>
@{cterm "if ((2::nat) < 3) then (if ((3::nat) < 2) then 20 + 1 else 20 + 2) else 20 + 3"}
  |> Simplifier.asm_full_rewrite @{context}
  |> assert @{cterm "22"}
\<close>
end


subsection \<open>Sketches for more meaningful congprocs\<close>

text \<open>One motivation for congprocs is the simplification of monadic terms which occur in the
context of the verification of imperative programs. We use Imperative_HOL as an example here.
In typical monadic programs we encounter lots of monadic binds and
guards aka assertions. Typical assertions protect against arithmetic overflows, dangling pointers
or might encode type information for some pointers. In particular when those assertions are
mechanically generated, e.g. by refinement proofs, there tends to be a lot of redundancy in
the assertions that are sprinkled all over the place in the program. Removing those redundant
guards by simplification can be utilised by congprocs.

\<close>

text \<open>
A first attempt for a congruence rule to propagate an assertion through a bind is the following:
We can assume the predicate when simplifying the 'body' \<^term>\<open>f\<close>:
\<close>
lemma assert_bind_cong':
  "(P x = P' x) \<Longrightarrow> (P x \<Longrightarrow> f = f') \<Longrightarrow> ((assert P x) \<bind> f) = ((assert P' x) \<bind> f')"
  by (auto simp add: assert_def bind_def simp add: execute_raise split: option.splits)

text \<open>Unfortunately this is not a plain congruence rule that the simplifier can work with.
The problem is that congruence rules only work on the head constant of the left hand side of
 the equation in the conclusion. This is \<^const>\<open>bind\<close>. But the rule is too specific as it only works
for binds where the first monadic action is an \<^const>\<open>assert\<close>. Fortunately congprocs offer
that flexibility. Like simprocs they can be triggered by patterns not only the head constant.

A slightly more abstract version, generalises the parameter \<^term>\<open>x\<close> for simplification of the body
\<^term>\<open>f\<close>. This also illustrates the introduction of bound variables that are passed along through
the \<^const>\<open>bind\<close>.
\<close>

lemma assert_bind_cong:
  "(P x = P' x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> f x = f' x) \<Longrightarrow> ((assert P x) \<bind> f) = ((assert P' x) \<bind> f')"
  by (auto simp add: assert_def bind_def simp add: execute_raise execute_return split: option.splits)

text \<open>Another typical use case is that a monadic action returns a tuple which is then propagated
through the binds. The tuple is naturally stated in 'eta expanded' form like \<^term>\<open>\<lambda>(x,y). f x y\<close> such that the
body can directly refer to the bound variables \<^term>\<open>x\<close> and \<^term>\<open>z\<close> and not via \<^const>\<open>fst\<close> and
 \<^const>\<open>snd\<close>.\<close>

lemma assert_bind_cong2':
  "(P a b = P' a b) \<Longrightarrow> (P a b \<Longrightarrow> f a b = f' a b) \<Longrightarrow>
  ((assert (\<lambda>(x,y). P x y) (a,b)) \<bind> (\<lambda>(x,y). f x y)) = ((assert (\<lambda>(x,y). P' x y) (a,b)) \<bind> (\<lambda>(x,y). f' x y))"
  apply (auto simp add: assert_def bind_def simp add: execute_raise execute_return
      split: option.splits)
  done

lemma assert_bind_cong2:
  "(P a b = P' a b) \<Longrightarrow> (\<And>a b. P a b \<Longrightarrow> f a b = f' a b) \<Longrightarrow>
  ((assert (\<lambda>(x,y). P x y) (a,b)) \<bind> (\<lambda>(x,y). f x y)) = ((assert (\<lambda>(x,y). P' x y) (a,b)) \<bind> (\<lambda>(x,y). f' x y))"
  apply (auto simp add: assert_def bind_def simp add: execute_raise execute_return
      split: option.splits)
  done

lemma assert_True_cond[simp]: "P x \<Longrightarrow> ((assert P x) \<bind> f) = f x"
  by (auto simp add: assert_def bind_def
      simp add: execute_return execute_raise split: option.splits)

simproc_setup passive congproc assert_bind_cong (\<open>(assert P x) \<bind> f\<close>) = \<open>
  K (K (K (SOME @{thm assert_bind_cong [cong_format]})))
\<close>

simproc_setup passive congproc assert_bind_cong2 (\<open>(assert P x) \<bind> f\<close>) = \<open>
  K (K (K (SOME @{thm assert_bind_cong2 [cong_format]})))
\<close>

experiment
begin
declare [[simproc add: assert_bind_cong]]
text \<open>The second assert is removed as expected.\<close>
ML_val \<open>
@{cterm "do {x <- assert P x; y <- assert P x; f y}"}
  |> (Simplifier.asm_full_rewrite @{context})
  |> assert_equiv @{cterm "assert P x \<bind> f"}
\<close>
end

experiment fixes a::nat
begin
declare [[simproc add: assert_bind_cong]]
text \<open>Does not work as expected due to issues with binding of the tuples\<close>
ML_val \<open>
@{cterm "do {(a, b) <- assert (\<lambda>(x,y). x < y) (a,b); (k,i) <- assert (\<lambda>(x,y). x < y)  (a, b); return (k < i)}"}
  |> (Simplifier.asm_full_rewrite @{context})
  |> assert_equiv @{cterm "assert (\<lambda>c. a < b) (a, b) \<bind>
      (\<lambda>x. case x of (a, b) \<Rightarrow> assert (\<lambda>c. a < b) (a, b) \<bind> (\<lambda>x. case x of (k, i) \<Rightarrow> return (k < i)))"}
\<close>
end

experiment fixes a::nat
begin
declare [[simproc add: assert_bind_cong2]]
text \<open>Works as expected. The second assert is removed and the condition is propagated to the final
 \<^const>\<open>return\<close>\<close>
ML_val \<open>
@{cterm "do {(a, b) <- assert (\<lambda>(x,y). x < y) (a,b); (k,i) <- assert (\<lambda>(x,y). x < y)  (a, b); return (k < i)}"}
  |> (Simplifier.asm_full_rewrite @{context})
  |> assert_equiv @{cterm "assert (\<lambda>(x, y). x < y) (a, b) \<bind> (\<lambda>(x, y). return True)"}
\<close>
end

text \<open>To properly handle tuples in general we cold of course refine our congproc to
analyse the arity of the \<^const>\<open>bind\<close> and then derive a variant of @{thm assert_bind_cong2} with the
corresponding arity, 3, 4, 5... We leave this as a exercise for the reader.

N.B. For the problem of tuple-splitting there sure are other solutions, e.g. normalising the
program with @{thm case_prod_conv} or @{thm case_prod_unfold}. The drawback is that this usually
diminishes the readability of the monadic expression. Moreover, from a performance perspective it
is usually better to split a rule like @{thm assert_bind_cong2}, which is abstract and of a fixed
known small size, compared to normalisation of an unknown user defined  monadic expression which might
be quite sizeable.
\<close>


subsection \<open>Customizing the context in congruence rules and congprocs\<close>

text \<open>
When the simplifier works on a term it manages its context in the simpset. In
particular when 'going under' an abstraction \<open>\<lambda>x. ...\<close> it introduces a fresh free variable \<^term>\<open>x\<close>,
substitutes it in the body and continues. Also when going under an implication \<^term>\<open>P \<Longrightarrow> C\<close> it
assumes \<^term>\<open>P\<close>, extracts simplification rules from \<^term>\<open>P\<close> which it adds to the simpset and
simplifies the conclusion \<^term>\<open>C\<close>. This pattern is what we typically encounter in congruence rules
like @{thm assert_bind_cong2} where we have a precondition like
 \<^term>\<open>\<And>a b. P a b \<Longrightarrow> f a b = f' a b\<close>. This advises the simplifier to fix \<^term>\<open>a\<close> and \<^term>\<open>b\<close>,
assume \<^term>\<open>P a b\<close>, extract simplification rules from that, and continue to simplify \<^term>\<open>f a b\<close>.

With congprocs we can go beyond this default behaviour of the simplifier as we are not restricted
to the format of congruence rules. In the end we have to deliver an equation but are free how we
derive it. A common building block of such more refined congprocs is that we
not only want to add \<^term>\<open>P a b\<close> to the simpset but want to enhance some other application specific
data with that premise, e.g. add it to a collection of named theorems or come up with some derived facts
that we want to offer some other tool (like another simproc, or solver).
The simpset already offers the possiblity to customise @{ML \<open>Simplifier.mksimps\<close>} which is a
function of type @{ML_type "Proof.context -> thm -> thm list"}. This function is used to derive equations
from a premise like \<^term>\<open>P a b\<close> when it is added by the simplifier. We have extended that
function to type @{ML_type "thm -> Proof.context -> thm list * Proof.context"} to give the user the
control to do additional modifications to the context:
@{ML Simplifier.get_mksimps_context}, @{ML Simplifier.set_mksimps_context}
The following contrived example illustrates the potential usage:
\<close>

definition EXTRACT :: "bool \<Rightarrow> bool" where "EXTRACT P = P"
definition UNPROTECT :: "bool \<Rightarrow> bool" where "UNPROTECT P = P"

lemma EXTRACT_TRUE_UNPROTECT_D: "EXTRACT P \<equiv> True \<Longrightarrow> (UNPROTECT P \<equiv> True)"
  by (simp add: EXTRACT_def UNPROTECT_def)

named_theorems my_theorems

text \<open>We modify @{ML Simplifier.mksimps} to derive a theorem about \<^term>\<open>UNPROTECT P\<close> from
 \<^term>\<open>EXTRACT P\<close> and add it to the named theorems @{thm my_theorems}.\<close>

setup \<open>
let
  fun my_mksimps old_mksimps thm ctxt =
    let
      val (thms, ctxt') = old_mksimps thm ctxt
      val thms' = map_filter (try (fn thm => @{thm EXTRACT_TRUE_UNPROTECT_D} OF [thm])) thms
      val _ = tracing ("adding: " ^ @{make_string} thms' ^ " to my_theorems")
      val ctxt'' = ctxt' |> Context.proof_map (fold (Named_Theorems.add_thm @{named_theorems my_theorems}) thms')
    in
      (thms, ctxt'' )
    end
in
  Context.theory_map (fn context =>
    let val old_mksimps = Simplifier.get_mksimps_context (Context.proof_of context)
    in context |> Simplifier.map_simpset (Simplifier.set_mksimps_context (my_mksimps old_mksimps)) end)
end
\<close>

text \<open>We provide a simproc that matches on \<^term>\<open>UNPROTECT P\<close> and tries to solve it
with rules in named theorems @{thm my_theorems}.\<close>
simproc_setup UNPROTECT (\<open>UNPROTECT P\<close>) = \<open>fn _ => fn ctxt => fn ct =>
  let
    val thms = Named_Theorems.get ctxt @{named_theorems my_theorems}
    val _ = tracing ("my_theorems: " ^ @{make_string} thms)
    val eq = Simplifier.rewrite (ctxt addsimps thms) ct
  in if Thm.is_reflexive eq then NONE else SOME eq end\<close>

lemma "EXTRACT P \<Longrightarrow> UNPROTECT P"
  supply [[simp_trace]]
  apply (simp)
  done

text \<open>Illustrate the antiquotation.\<close>
ML \<open>
val conproc1 = \<^simproc_setup>\<open>passive weak_congproc if_cong1  ("if x then a else b") =
  \<open>(K (K (K (SOME @{thm if_cong [cong_format]}))))\<close>\<close>
\<close>

end
