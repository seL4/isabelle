(*<*)theory Axioms = Overloading:(*>*)

subsection{*Axioms*}


text{*Now we want to attach axioms to our classes. Then we can reason on the
level of classes and the results will be applicable to all types in a class,
just as in axiomatic mathematics. These ideas are demonstrated by means of
our above ordering relations.
*}

subsubsection{*Partial orders*}

text{*
A \emph{partial order} is a subclass of @{text ordrel}
where certain axioms need to hold:
*}

axclass parord < ordrel
refl:    "x <<= x"
trans:   "\<lbrakk> x <<= y; y <<= z \<rbrakk> \<Longrightarrow> x <<= z"
antisym: "\<lbrakk> x <<= y; y <<= x \<rbrakk> \<Longrightarrow> x = y"
less_le: "x << y = (x <<= y \<and> x \<noteq> y)"

text{*\noindent
The first three axioms are the familiar ones, and the final one
requires that @{text"<<"} and @{text"<<="} are related as expected.
Note that behind the scenes, Isabelle has restricted the axioms to class
@{text parord}. For example, this is what @{thm[source]refl} really looks like:
@{thm[show_types]refl}.

We can now prove simple theorems in this abstract setting, for example
that @{text"<<"} is not symmetric:
*}

lemma [simp]: "(x::'a::parord) << y \<Longrightarrow> (\<not> y << x) = True";

txt{*\noindent
The conclusion is not simply @{prop"\<not> y << x"} because the preprocessor
of the simplifier would turn this into @{prop"y << x = False"}, thus yielding
a nonterminating rewrite rule. In the above form it is a generally useful
rule.
The type constraint is necessary because otherwise Isabelle would only assume
@{text"'a::ordrel"} (as required in the type of @{text"<<"}), in
which case the proposition is not a theorem.  The proof is easy:
*}

by(simp add:less_le antisym);

text{* We could now continue in this vein and develop a whole theory of
results about partial orders. Eventually we will want to apply these results
to concrete types, namely the instances of the class. Thus we first need to
prove that the types in question, for example @{typ bool}, are indeed
instances of @{text parord}:*}

instance bool :: parord
apply intro_classes;

txt{*\noindent
This time @{text intro_classes} leaves us with the four axioms,
specialized to type @{typ bool}, as subgoals:
@{goals[display,show_types,indent=0]}
Fortunately, the proof is easy for blast, once we have unfolded the definitions
of @{text"<<"} and @{text"<<="} at @{typ bool}:
*}

apply(simp_all (no_asm_use) only: le_bool_def less_bool_def);
by(blast, blast, blast, blast);

text{*\noindent
Can you figure out why we have to include @{text"(no_asm_use)"}?

We can now apply our single lemma above in the context of booleans:
*}

lemma "(P::bool) << Q \<Longrightarrow> \<not>(Q << P)";
by simp;

text{*\noindent
The effect is not stunning but demonstrates the principle.  It also shows
that tools like the simplifier can deal with generic rules as well. Moreover,
it should be clear that the main advantage of the axiomatic method is that
theorems can be proved in the abstract and one does not need to repeat the
proof for each instance.
*}

subsubsection{*Linear orders*}

text{* If any two elements of a partial order are comparable it is a
\emph{linear} or \emph{total} order: *}

axclass linord < parord
total: "x <<= y \<or> y <<= x"

text{*\noindent
By construction, @{text linord} inherits all axioms from @{text parord}.
Therefore we can show that totality can be expressed in terms of @{text"<<"}
as follows:
*}

lemma "\<And>x::'a::linord. x<<y \<or> x=y \<or> y<<x";
apply(simp add: less_le);
apply(insert total);
apply blast;
done

text{*
Linear orders are an example of subclassing by construction, which is the most
common case. It is also possible to prove additional subclass relationships
later on, i.e.\ subclassing by proof. This is the topic of the following
section.
*}

subsubsection{*Strict orders*}

text{*
An alternative axiomatization of partial orders takes @{text"<<"} rather than
@{text"<<="} as the primary concept. The result is a \emph{strict} order:
*}

axclass strord < ordrel
irrefl:     "\<not> x << x"
less_trans: "\<lbrakk> x << y; y << z \<rbrakk> \<Longrightarrow> x << z"
le_less:    "x <<= y = (x << y \<or> x = y)"

text{*\noindent
It is well known that partial orders are the same as strict orders. Let us
prove one direction, namely that partial orders are a subclass of strict
orders. The proof follows the ususal pattern: *}

instance parord < strord
apply intro_classes;
apply(simp_all (no_asm_use) add:less_le);
  apply(blast intro: trans antisym);
 apply(blast intro: refl);
done

text{*\noindent
The result is the following subclass diagram:
\[
\begin{array}{c}
\isa{term}\\
|\\
\isa{ordrel}\\
|\\
\isa{strord}\\
|\\
\isa{parord}
\end{array}
\]

In general, the subclass diagram must be acyclic. Therefore Isabelle will
complain if you also prove the relationship @{text"strord < parord"}.
Multiple inheritance is however permitted.

This finishes our demonstration of type classes based on orderings.  We
remind our readers that \isa{Main} contains a much more developed theory of
orderings phrased in terms of the usual @{text"\<le>"} and @{text"<"}.
It is recommended that, if possible,
you base your own ordering relations on this theory.
*}

(*
instance strord < parord
apply intro_classes;
apply(simp_all (no_asm_use) add:le_less);
apply(blast intro: less_trans);
apply(erule disjE);
apply(erule disjE);
apply(rule irrefl[THEN notE]);
apply(rule less_trans, assumption, assumption);
apply blast;apply blast;
apply(blast intro: irrefl[THEN notE]);
done
*)

subsubsection{*Inconsistencies*}

text{* The reader may be wondering what happens if we, maybe accidentally,
attach an inconsistent set of axioms to a class. So far we have always
avoided to add new axioms to HOL for fear of inconsistencies and suddenly it
seems that we are throwing all caution to the wind. So why is there no
problem?

The point is that by construction, all type variables in the axioms of an
\isacommand{axclass} are automatically constrained with the class being
defined (as shown for axiom @{thm[source]refl} above). These constraints are
always carried around and Isabelle takes care that they are never lost,
unless the type variable is instantiated with a type that has been shown to
belong to that class. Thus you may be able to prove @{prop False}
from your axioms, but Isabelle will remind you that this
theorem has the hidden hypothesis that the class is non-empty.
*}

(*
axclass false<"term"
false: "x \<noteq> x";

lemma "False";
by(rule notE[OF false HOL.refl]);
*)
(*<*)end(*>*)
