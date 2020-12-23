(*<*)theory Axioms imports Overloading "../Setup" begin(*>*)

subsection \<open>Axioms\<close>

text \<open>Attaching axioms to our classes lets us reason on the level of
classes.  The results will be applicable to all types in a class, just
as in axiomatic mathematics.

\begin{warn}
Proofs in this section use structured \emph{Isar} proofs, which are not
covered in this tutorial; but see @{cite "Nipkow-TYPES02"}.%
\end{warn}\<close>

subsubsection \<open>Semigroups\<close>

text\<open>We specify \emph{semigroups} as subclass of \<^class>\<open>plus\<close>:\<close>

class semigroup = plus +
  assumes assoc: "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"

text \<open>\noindent This @{command class} specification requires that
all instances of \<^class>\<open>semigroup\<close> obey @{fact "assoc:"}~@{prop
[source] "\<And>x y z :: 'a::semigroup. (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"}.

We can use this class axiom to derive further abstract theorems
relative to class \<^class>\<open>semigroup\<close>:\<close>

lemma assoc_left:
  fixes x y z :: "'a::semigroup"
  shows "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
  using assoc by (rule sym)

text \<open>\noindent The \<^class>\<open>semigroup\<close> constraint on type \<^typ>\<open>'a\<close> restricts instantiations of \<^typ>\<open>'a\<close> to types of class
\<^class>\<open>semigroup\<close> and during the proof enables us to use the fact
@{fact assoc} whose type parameter is itself constrained to class
\<^class>\<open>semigroup\<close>.  The main advantage of classes is that theorems
can be proved in the abstract and freely reused for each instance.

On instantiation, we have to give a proof that the given operations
obey the class axioms:\<close>

instantiation nat :: semigroup
begin

instance proof

txt \<open>\noindent The proof opens with a default proof step, which for
instance judgements invokes method @{method intro_classes}.\<close>


  fix m n q :: nat
  show "(m \<oplus> n) \<oplus> q = m \<oplus> (n \<oplus> q)"
    by (induct m) simp_all
qed

end

text \<open>\noindent Again, the interesting things enter the stage with
parametric types:\<close>

instantiation prod :: (semigroup, semigroup) semigroup
begin

instance proof
  fix p\<^sub>1 p\<^sub>2 p\<^sub>3 :: "'a::semigroup \<times> 'b::semigroup"
  show "p\<^sub>1 \<oplus> p\<^sub>2 \<oplus> p\<^sub>3 = p\<^sub>1 \<oplus> (p\<^sub>2 \<oplus> p\<^sub>3)"
    by (cases p\<^sub>1, cases p\<^sub>2, cases p\<^sub>3) (simp add: assoc)

txt \<open>\noindent Associativity of product semigroups is established
using the hypothetical associativity @{fact assoc} of the type
components, which holds due to the \<^class>\<open>semigroup\<close> constraints
imposed on the type components by the @{command instance} proposition.
Indeed, this pattern often occurs with parametric types and type
classes.\<close>

qed

end

subsubsection \<open>Monoids\<close>

text \<open>We define a subclass \<open>monoidl\<close> (a semigroup with a
left-hand neutral) by extending \<^class>\<open>semigroup\<close> with one additional
parameter \<open>neutral\<close> together with its property:\<close>

class monoidl = semigroup +
  fixes neutral :: "'a" ("\<zero>")
  assumes neutl: "\<zero> \<oplus> x = x"

text \<open>\noindent Again, we prove some instances, by providing
suitable parameter definitions and proofs for the additional
specifications.\<close>

instantiation nat :: monoidl
begin

definition
  neutral_nat_def: "\<zero> = (0::nat)"

instance proof
  fix n :: nat
  show "\<zero> \<oplus> n = n"
    unfolding neutral_nat_def by simp
qed

end

text \<open>\noindent In contrast to the examples above, we here have both
specification of class operations and a non-trivial instance proof.

This covers products as well:
\<close>

instantiation prod :: (monoidl, monoidl) monoidl
begin

definition
  neutral_prod_def: "\<zero> = (\<zero>, \<zero>)"

instance proof
  fix p :: "'a::monoidl \<times> 'b::monoidl"
  show "\<zero> \<oplus> p = p"
    by (cases p) (simp add: neutral_prod_def neutl)
qed

end

text \<open>\noindent Fully-fledged monoids are modelled by another
subclass which does not add new parameters but tightens the
specification:\<close>

class monoid = monoidl +
  assumes neutr: "x \<oplus> \<zero> = x"

text \<open>\noindent Corresponding instances for \<^typ>\<open>nat\<close> and products
are left as an exercise to the reader.\<close>

subsubsection \<open>Groups\<close>

text \<open>\noindent To finish our small algebra example, we add a \<open>group\<close> class:\<close>

class group = monoidl +
  fixes inv :: "'a \<Rightarrow> 'a" ("\<div> _" [81] 80)
  assumes invl: "\<div> x \<oplus> x = \<zero>"

text \<open>\noindent We continue with a further example for abstract
proofs relative to type classes:\<close>

lemma left_cancel:
  fixes x y z :: "'a::group"
  shows "x \<oplus> y = x \<oplus> z \<longleftrightarrow> y = z"
proof
  assume "x \<oplus> y = x \<oplus> z"
  then have "\<div> x \<oplus> (x \<oplus> y) = \<div> x \<oplus> (x \<oplus> z)" by simp
  then have "(\<div> x \<oplus> x) \<oplus> y = (\<div> x \<oplus> x) \<oplus> z" by (simp add: assoc)
  then show "y = z" by (simp add: invl neutl)
next
  assume "y = z"
  then show "x \<oplus> y = x \<oplus> z" by simp
qed

text \<open>\noindent Any \<open>group\<close> is also a \<open>monoid\<close>; this
can be made explicit by claiming an additional subclass relation,
together with a proof of the logical difference:\<close>

instance group \<subseteq> monoid
proof
  fix x
  from invl have "\<div> x \<oplus> x = \<zero>" .
  then have "\<div> x \<oplus> (x \<oplus> \<zero>) = \<div> x \<oplus> x"
    by (simp add: neutl invl assoc [symmetric])
  then show "x \<oplus> \<zero> = x" by (simp add: left_cancel)
qed

text \<open>\noindent The proof result is propagated to the type system,
making \<open>group\<close> an instance of \<open>monoid\<close> by adding an
additional edge to the graph of subclass relation; see also
Figure~\ref{fig:subclass}.

\begin{figure}[htbp]
 \begin{center}
   \small
   \unitlength 0.6mm
   \begin{picture}(40,60)(0,0)
     \put(20,60){\makebox(0,0){\<open>semigroup\<close>}}
     \put(20,40){\makebox(0,0){\<open>monoidl\<close>}}
     \put(00,20){\makebox(0,0){\<open>monoid\<close>}}
     \put(40,00){\makebox(0,0){\<open>group\<close>}}
     \put(20,55){\vector(0,-1){10}}
     \put(15,35){\vector(-1,-1){10}}
     \put(25,35){\vector(1,-3){10}}
   \end{picture}
   \hspace{8em}
   \begin{picture}(40,60)(0,0)
     \put(20,60){\makebox(0,0){\<open>semigroup\<close>}}
     \put(20,40){\makebox(0,0){\<open>monoidl\<close>}}
     \put(00,20){\makebox(0,0){\<open>monoid\<close>}}
     \put(40,00){\makebox(0,0){\<open>group\<close>}}
     \put(20,55){\vector(0,-1){10}}
     \put(15,35){\vector(-1,-1){10}}
     \put(05,15){\vector(3,-1){30}}
   \end{picture}
   \caption{Subclass relationship of monoids and groups:
      before and after establishing the relationship
      \<open>group \<subseteq> monoid\<close>;  transitive edges are left out.}
   \label{fig:subclass}
 \end{center}
\end{figure}
\<close>

subsubsection \<open>Inconsistencies\<close>

text \<open>The reader may be wondering what happens if we attach an
inconsistent set of axioms to a class. So far we have always avoided
to add new axioms to HOL for fear of inconsistencies and suddenly it
seems that we are throwing all caution to the wind. So why is there no
problem?

The point is that by construction, all type variables in the axioms of
a \isacommand{class} are automatically constrained with the class
being defined (as shown for axiom @{thm[source]refl} above). These
constraints are always carried around and Isabelle takes care that
they are never lost, unless the type variable is instantiated with a
type that has been shown to belong to that class. Thus you may be able
to prove \<^prop>\<open>False\<close> from your axioms, but Isabelle will remind you
that this theorem has the hidden hypothesis that the class is
non-empty.

Even if each individual class is consistent, intersections of
(unrelated) classes readily become inconsistent in practice. Now we
know this need not worry us.\<close>


subsubsection\<open>Syntactic Classes and Predefined Overloading\<close>

text \<open>In our algebra example, we have started with a \emph{syntactic
class} \<^class>\<open>plus\<close> which only specifies operations but no axioms; it
would have been also possible to start immediately with class \<^class>\<open>semigroup\<close>, specifying the \<open>\<oplus>\<close> operation and associativity at
the same time.

Which approach is more appropriate depends.  Usually it is more
convenient to introduce operations and axioms in the same class: then
the type checker will automatically insert the corresponding class
constraints whenever the operations occur, reducing the need of manual
annotations.  However, when operations are decorated with popular
syntax, syntactic classes can be an option to re-use the syntax in
different contexts; this is indeed the way most overloaded constants
in HOL are introduced, of which the most important are listed in
Table~\ref{tab:overloading} in the appendix.  Section
\ref{sec:numeric-classes} covers a range of corresponding classes
\emph{with} axioms.

Further note that classes may contain axioms but \emph{no} operations.
An example is class \<^class>\<open>finite\<close> from theory \<^theory>\<open>HOL.Finite_Set\<close>
which specifies a type to be finite: @{lemma [source] "finite (UNIV :: 'a::finite
set)" by (fact finite_UNIV)}.\<close>

(*<*)end(*>*)
