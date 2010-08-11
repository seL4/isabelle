(*<*)theory Axioms imports Overloading Setup begin(*>*)

subsection {* Axioms *}

text {* Attaching axioms to our classes lets us reason on the level of
classes.  The results will be applicable to all types in a class, just
as in axiomatic mathematics.

\begin{warn}
Proofs in this section use structured \emph{Isar} proofs, which are not
covered in this tutorial; but see \cite{Nipkow-TYPES02}.%
\end{warn} *}

subsubsection {* Semigroups *}

text{* We specify \emph{semigroups} as subclass of @{class plus}: *}

class semigroup = plus +
  assumes assoc: "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"

text {* \noindent This @{command class} specification requires that
all instances of @{class semigroup} obey @{fact "assoc:"}~@{prop
[source] "\<And>x y z \<Colon> 'a\<Colon>semigroup. (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"}.

We can use this class axiom to derive further abstract theorems
relative to class @{class semigroup}: *}

lemma assoc_left:
  fixes x y z :: "'a\<Colon>semigroup"
  shows "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
  using assoc by (rule sym)

text {* \noindent The @{class semigroup} constraint on type @{typ
"'a"} restricts instantiations of @{typ "'a"} to types of class
@{class semigroup} and during the proof enables us to use the fact
@{fact assoc} whose type parameter is itself constrained to class
@{class semigroup}.  The main advantage of classes is that theorems
can be proved in the abstract and freely reused for each instance.

On instantiation, we have to give a proof that the given operations
obey the class axioms: *}

instantiation nat :: semigroup
begin

instance proof

txt {* \noindent The proof opens with a default proof step, which for
instance judgements invokes method @{method intro_classes}. *}


  fix m n q :: nat
  show "(m \<oplus> n) \<oplus> q = m \<oplus> (n \<oplus> q)"
    by (induct m) simp_all
qed

end

text {* \noindent Again, the interesting things enter the stage with
parametric types: *}

instantiation prod :: (semigroup, semigroup) semigroup
begin

instance proof
  fix p\<^isub>1 p\<^isub>2 p\<^isub>3 :: "'a\<Colon>semigroup \<times> 'b\<Colon>semigroup"
  show "p\<^isub>1 \<oplus> p\<^isub>2 \<oplus> p\<^isub>3 = p\<^isub>1 \<oplus> (p\<^isub>2 \<oplus> p\<^isub>3)"
    by (cases p\<^isub>1, cases p\<^isub>2, cases p\<^isub>3) (simp add: assoc)

txt {* \noindent Associativity of product semigroups is established
using the hypothetical associativity @{fact assoc} of the type
components, which holds due to the @{class semigroup} constraints
imposed on the type components by the @{command instance} proposition.
Indeed, this pattern often occurs with parametric types and type
classes. *}

qed

end

subsubsection {* Monoids *}

text {* We define a subclass @{text monoidl} (a semigroup with a
left-hand neutral) by extending @{class semigroup} with one additional
parameter @{text neutral} together with its property: *}

class monoidl = semigroup +
  fixes neutral :: "'a" ("\<zero>")
  assumes neutl: "\<zero> \<oplus> x = x"

text {* \noindent Again, we prove some instances, by providing
suitable parameter definitions and proofs for the additional
specifications. *}

instantiation nat :: monoidl
begin

definition
  neutral_nat_def: "\<zero> = (0\<Colon>nat)"

instance proof
  fix n :: nat
  show "\<zero> \<oplus> n = n"
    unfolding neutral_nat_def by simp
qed

end

text {* \noindent In contrast to the examples above, we here have both
specification of class operations and a non-trivial instance proof.

This covers products as well:
*}

instantiation prod :: (monoidl, monoidl) monoidl
begin

definition
  neutral_prod_def: "\<zero> = (\<zero>, \<zero>)"

instance proof
  fix p :: "'a\<Colon>monoidl \<times> 'b\<Colon>monoidl"
  show "\<zero> \<oplus> p = p"
    by (cases p) (simp add: neutral_prod_def neutl)
qed

end

text {* \noindent Fully-fledged monoids are modelled by another
subclass which does not add new parameters but tightens the
specification: *}

class monoid = monoidl +
  assumes neutr: "x \<oplus> \<zero> = x"

text {* \noindent Corresponding instances for @{typ nat} and products
are left as an exercise to the reader. *}

subsubsection {* Groups *}

text {* \noindent To finish our small algebra example, we add a @{text
group} class: *}

class group = monoidl +
  fixes inv :: "'a \<Rightarrow> 'a" ("\<div> _" [81] 80)
  assumes invl: "\<div> x \<oplus> x = \<zero>"

text {* \noindent We continue with a further example for abstract
proofs relative to type classes: *}

lemma left_cancel:
  fixes x y z :: "'a\<Colon>group"
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

text {* \noindent Any @{text "group"} is also a @{text "monoid"}; this
can be made explicit by claiming an additional subclass relation,
together with a proof of the logical difference: *}

instance group \<subseteq> monoid
proof
  fix x
  from invl have "\<div> x \<oplus> x = \<zero>" .
  then have "\<div> x \<oplus> (x \<oplus> \<zero>) = \<div> x \<oplus> x"
    by (simp add: neutl invl assoc [symmetric])
  then show "x \<oplus> \<zero> = x" by (simp add: left_cancel)
qed

text {* \noindent The proof result is propagated to the type system,
making @{text group} an instance of @{text monoid} by adding an
additional edge to the graph of subclass relation; see also
Figure~\ref{fig:subclass}.

\begin{figure}[htbp]
 \begin{center}
   \small
   \unitlength 0.6mm
   \begin{picture}(40,60)(0,0)
     \put(20,60){\makebox(0,0){@{text semigroup}}}
     \put(20,40){\makebox(0,0){@{text monoidl}}}
     \put(00,20){\makebox(0,0){@{text monoid}}}
     \put(40,00){\makebox(0,0){@{text group}}}
     \put(20,55){\vector(0,-1){10}}
     \put(15,35){\vector(-1,-1){10}}
     \put(25,35){\vector(1,-3){10}}
   \end{picture}
   \hspace{8em}
   \begin{picture}(40,60)(0,0)
     \put(20,60){\makebox(0,0){@{text semigroup}}}
     \put(20,40){\makebox(0,0){@{text monoidl}}}
     \put(00,20){\makebox(0,0){@{text monoid}}}
     \put(40,00){\makebox(0,0){@{text group}}}
     \put(20,55){\vector(0,-1){10}}
     \put(15,35){\vector(-1,-1){10}}
     \put(05,15){\vector(3,-1){30}}
   \end{picture}
   \caption{Subclass relationship of monoids and groups:
      before and after establishing the relationship
      @{text "group \<subseteq> monoid"};  transitive edges are left out.}
   \label{fig:subclass}
 \end{center}
\end{figure}
*}

subsubsection {* Inconsistencies *}

text {* The reader may be wondering what happens if we attach an
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
to prove @{prop False} from your axioms, but Isabelle will remind you
that this theorem has the hidden hypothesis that the class is
non-empty.

Even if each individual class is consistent, intersections of
(unrelated) classes readily become inconsistent in practice. Now we
know this need not worry us. *}


subsubsection{* Syntactic Classes and Predefined Overloading *}

text {* In our algebra example, we have started with a \emph{syntactic
class} @{class plus} which only specifies operations but no axioms; it
would have been also possible to start immediately with class @{class
semigroup}, specifying the @{text "\<oplus>"} operation and associativity at
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
An example is class @{class finite} from theory @{theory Finite_Set}
which specifies a type to be finite: @{lemma [source] "finite (UNIV \<Colon> 'a\<Colon>finite
set)" by (fact finite_UNIV)}. *}

(*<*)end(*>*)
