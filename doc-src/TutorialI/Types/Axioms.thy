(*<*)theory Axioms = Overloading:(*>*)

subsection{*Axioms*}


text{*Attaching axioms to our classes lets us reason on the
level of classes.  The results will be applicable to all types in a class,
just as in axiomatic mathematics.  These ideas are demonstrated by means of
our ordering relations.
*}

subsubsection{*Partial Orders*}

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
@{text parord}. For example, the axiom @{thm[source]refl} really is
@{thm[show_sorts]refl}.

We have not made @{thm[source]less_le} a global definition because it would
fix once and for all that @{text"<<"} is defined in terms of @{text"<<="} and
never the other way around. Below you will see why we want to avoid this
asymmetry. The drawback of our choice is that
we need to define both @{text"<<="} and @{text"<<"} for each instance.

We can now prove simple theorems in this abstract setting, for example
that @{text"<<"} is not symmetric:
*}

lemma [simp]: "(x::'a::parord) << y \<Longrightarrow> (\<not> y << x) = True";

txt{*\noindent
The conclusion is not just @{prop"\<not> y << x"} because the 
simplifier's preprocessor (see \S\ref{sec:simp-preprocessor})
would turn it into @{prop"y << x = False"}, yielding
a nonterminating rewrite rule.  
(It would be used to try to prove its own precondition \emph{ad
    infinitum}.)
In the form above, the rule is useful.
The type constraint is necessary because otherwise Isabelle would only assume
@{text"'a::ordrel"} (as required in the type of @{text"<<"}), 
when the proposition is not a theorem.  The proof is easy:
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
@{subgoals[display,show_types,indent=0]}
Fortunately, the proof is easy for \isa{blast}
once we have unfolded the definitions
of @{text"<<"} and @{text"<<="} at type @{typ bool}:
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
The effect is not stunning, but it demonstrates the principle.  It also shows
that tools like the simplifier can deal with generic rules.
The main advantage of the axiomatic method is that
theorems can be proved in the abstract and freely reused for each instance.
*}

subsubsection{*Linear Orders*}

text{* If any two elements of a partial order are comparable it is a
\textbf{linear} or \textbf{total} order: *}

axclass linord < parord
linear: "x <<= y \<or> y <<= x"

text{*\noindent
By construction, @{text linord} inherits all axioms from @{text parord}.
Therefore we can show that linearity can be expressed in terms of @{text"<<"}
as follows:
*}

lemma "\<And>x::'a::linord. x << y \<or> x = y \<or> y << x";
apply(simp add: less_le);
apply(insert linear);
apply blast;
done

text{*
Linear orders are an example of subclassing\index{subclasses}
by construction, which is the most
common case.  Subclass relationships can also be proved.  
This is the topic of the following
paragraph.
*}

subsubsection{*Strict Orders*}

text{*
An alternative axiomatization of partial orders takes @{text"<<"} rather than
@{text"<<="} as the primary concept. The result is a \textbf{strict} order:
*}

axclass strord < ordrel
irrefl:     "\<not> x << x"
less_trans: "\<lbrakk> x << y; y << z \<rbrakk> \<Longrightarrow> x << z"
le_less:    "x <<= y = (x << y \<or> x = y)"

text{*\noindent
It is well known that partial orders are the same as strict orders. Let us
prove one direction, namely that partial orders are a subclass of strict
orders. *}

instance parord < strord
apply intro_classes;

txt{*\noindent
@{subgoals[display,show_sorts]}
Assuming @{text"'a :: parord"}, the three axioms of class @{text strord}
are easily proved:
*}

  apply(simp_all (no_asm_use) add:less_le);
 apply(blast intro: trans antisym);
apply(blast intro: refl);
done

text{*
The subclass relation must always be acyclic. Therefore Isabelle will
complain if you also prove the relationship @{text"strord < parord"}.
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

subsubsection{*Multiple Inheritance and Sorts*}

text{*
A class may inherit from more than one direct superclass. This is called
\bfindex{multiple inheritance}.  For example, we could define
the classes of well-founded orderings and well-orderings:
*}

axclass wford < parord
wford: "wf {(y,x). y << x}"

axclass wellord < linord, wford

text{*\noindent
The last line expresses the usual definition: a well-ordering is a linear
well-founded ordering. The result is the subclass diagram in
Figure~\ref{fig:subclass}.

\begin{figure}[htbp]
\[
\begin{array}{r@ {}r@ {}c@ {}l@ {}l}
& & \isa{term}\\
& & |\\
& & \isa{ordrel}\\
& & |\\
& & \isa{strord}\\
& & |\\
& & \isa{parord} \\
& / & & \backslash \\
\isa{linord} & & & & \isa{wford} \\
& \backslash & & / \\
& & \isa{wellord}
\end{array}
\]
\caption{Subclass Diagram}
\label{fig:subclass}
\end{figure}

Since class @{text wellord} does not introduce any new axioms, it can simply
be viewed as the intersection of the two classes @{text linord} and @{text
wford}. Such intersections need not be given a new name but can be created on
the fly: the expression $\{C@1,\dots,C@n\}$, where the $C@i$ are classes,
represents the intersection of the $C@i$. Such an expression is called a
\textbf{sort},\index{sorts} and sorts can appear in most places where we have only shown
classes so far, for example in type constraints: @{text"'a::{linord,wford}"}.
In fact, @{text"'a::C"} is short for @{text"'a::{C}"}.
However, we do not pursue this rarefied concept further.

This concludes our demonstration of type classes based on orderings.  We
remind our readers that \isa{Main} contains a theory of
orderings phrased in terms of the usual @{text"\<le>"} and @{text"<"}.
If possible, base your own ordering relations on this theory.
*}

subsubsection{*Inconsistencies*}

text{* The reader may be wondering what happens if we
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

Even if each individual class is consistent, intersections of (unrelated)
classes readily become inconsistent in practice. Now we know this need not
worry us.
*}

(*
axclass false<"term"
false: "x \<noteq> x";

lemma "False";
by(rule notE[OF false HOL.refl]);
*)
(*<*)end(*>*)
